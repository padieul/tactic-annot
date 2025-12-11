"""Nebius API autoformalization using OpenAI-compatible interface."""

import os
import concurrent.futures
from typing import List, Optional, Callable, Tuple
from pathlib import Path
from openai import OpenAI

from .base import AesopAgentBase, AesopisationRequest, AesopisationResult


def load_prompt(filename: str) -> str:
    """Load a prompt from the prompts directory.
    
    Args:
        filename: Name of the prompt file (e.g., 'system_prompt.txt')
        
    Returns:
        The content of the prompt file
    """
    prompts_dir = Path(__file__).parent / "prompts"
    prompt_path = prompts_dir / filename
    
    if not prompt_path.exists():
        raise FileNotFoundError(f"Prompt file not found: {prompt_path}")
    
    return prompt_path.read_text(encoding='utf-8')


class AesopAgent(AesopAgentBase):
    """Nebius Studio API autoformalization (Qwen models).

    Uses Nebius Studio's OpenAI-compatible API for autoformalization.
    Requires NEBIUS_API_KEY environment variable.
    """

    def __init__(
        self,
        model: str = "Qwen/Qwen3-Coder-30B-A3B-Instruct",
        api_key: Optional[str] = None,
        base_url: str = "https://api.studio.nebius.ai/v1/",
        system_prompt: Optional[str] = None,
        retry_system_prompt: Optional[str] = None,
        default_temperature: float = 0.1,
    ):
        """Initialize Nebius API autoformalization.

        Args:
            model: Nebius model ID (default: Qwen3-Coder-30B)
            api_key: Nebius API key (default: read from NEBIUS_API_KEY env var)
            base_url: Nebius API base URL
            system_prompt: Custom system prompt (default: loaded from prompts/system_prompt.txt)
            retry_system_prompt: Custom system prompt for retries (default: loaded from prompts/retry_prompt.txt)
            default_temperature: Default temperature for sampling
        """
        super().__init__(model_name=f"nebius-{model.split('/')[-1]}")
        self.model = model
        self.base_url = base_url
        
        # Load prompts from files if not provided
        self.system_prompt = system_prompt or load_prompt("system_prompt.txt")
        self.retry_system_prompt = retry_system_prompt or load_prompt("retry_prompt.txt")
        self.default_temperature = default_temperature

        # Get API key from parameter or environment
        self.api_key = api_key or os.environ.get("NEBIUS_API_KEY")
        if not self.api_key:
            raise ValueError(
                "NEBIUS_API_KEY not found. Set it via environment variable or pass to constructor."
            )

        self._client: Optional[OpenAI] = None

    def initialize(self) -> None:
        """Initialize OpenAI client for Nebius API."""
        if self._initialized:
            return

        self._client = OpenAI(base_url=self.base_url, api_key=self.api_key)
        self._initialized = True
        print(f"Connected to Nebius API ({self.model})")

    def shutdown(self) -> None:
        """Clean up resources."""
        if self._client is not None:
            self._client.close()
            self._client = None
        super().shutdown()

    def _build_messages(self, request: AesopisationRequest) -> List[dict]:
        """Build messages for API request."""
        # Use retry prompt if there are previous attempts
        is_retry = request.previous_attempts and len(request.previous_attempts) > 0
        system_prompt = self.retry_system_prompt if is_retry else self.system_prompt
        
        messages = [{"role": "system", "content": system_prompt}]

        # Add context if provided
        if request.context:
            messages.append(
                {
                    "role": "user",
                    "content": f"Context (existing Lean 4 code):\n```lean4\n{request.context}\n```",
                }
            )
            messages.append(
                {
                    "role": "assistant",
                    "content": "I'll use these definitions when formalizing.",
                }
            )

        # Add previous attempts with their errors if this is a retry
        if is_retry:
            attempts_text = "Previous failed attempts:\n\n"
            for i, attempt in enumerate(request.previous_attempts, 1):
                attempts_text += f"Attempt {i}:\n```lean4\n{attempt['attempt']}\n```\n"
                attempts_text += f"Error:\n```\n{attempt['error']}\n```\n\n"
            
            messages.append({
                "role": "user",
                "content": attempts_text + f"\nOriginal theorem with working proof:\n```lean4\n{request.lean_theorem_str}\n```\n\nPlease generate a NEW aesop-based proof that avoids these errors. Try a different approach!"
            })
        else:
            # Add main request - the original theorem with full proof
            messages.append({
                "role": "user", 
                "content": f"Convert this theorem to use aesop:\n\n```lean4\n{request.lean_theorem_str}\n```"
            })

        return messages

    def _extract_lean_code(self, text: str) -> str:
        """Extract Lean code from response, removing markdown if present."""
        import re

        # Remove markdown code blocks if present
        patterns = [
            r"```lean4?\s*\n(.*?)```",
            r"```\s*\n(.*?)```",
        ]

        for pattern in patterns:
            match = re.search(pattern, text, re.DOTALL)
            if match:
                return match.group(1).strip()

        # Return as-is if no code block found
        return text.strip()

    def autoformalize(
        self, request: AesopisationRequest
    ) -> AesopisationResult:
        """Autoformalize using Nebius API."""
        if not self._initialized:
            self.initialize()

        try:
            messages = self._build_messages(request)

            # Use request temperature or default
            temperature = (
                request.temperature
                if request.temperature > 0
                else self.default_temperature
            )

            # Call Nebius API
            response = self._client.chat.completions.create(
                model=self.model,
                messages=messages,
                temperature=temperature,
                max_tokens=request.max_tokens,
            )

            # Extract result
            raw_content = response.choices[0].message.content
            formal_statement = self._extract_lean_code(raw_content)

            return AesopisationResult(
                formal_statement=formal_statement,
                success=bool(formal_statement),
                metadata={
                    "raw_output": raw_content,
                    "model": self.model,
                    "finish_reason": response.choices[0].finish_reason,
                    "usage": response.usage.model_dump() if response.usage else None,
                },
            )

        except Exception as e:
            return AesopisationResult(
                formal_statement="",
                success=False,
                error_message=str(e),
                metadata={"model": self.model},
            )

    def generate_multiple_versions(
        self, request: AesopisationRequest
    ) -> List[AesopisationResult]:
        """Generate multiple different proof versions in parallel.
        
        Uses the n_versions field from the request to generate multiple
        independent proof attempts with varied temperatures for diversity.
        
        Args:
            request: AesopisationRequest with n_versions set
            
        Returns:
            List of AesopisationResult objects, one per version
        """
        if not self._initialized:
            self.initialize()
        
        n_versions = request.n_versions
        if n_versions <= 1:
            return [self.autoformalize(request)]
        
        # Create requests with varied temperatures for diversity
        base_temp = request.temperature if request.temperature > 0 else self.default_temperature
        temp_variations = [
            base_temp,  # Original temperature
            base_temp * 0.5,  # Lower temp for more deterministic
            base_temp * 1.5,  # Higher temp for more creativity
            base_temp * 2.0,  # Even higher for wild attempts
            0.1,  # Very low
            0.3,  # Low
            0.7,  # Medium-high
            1.0,  # High
            0.2,  # Low-medium
            0.8,  # Medium-high
        ]
        
        def generate_one(version_idx: int) -> AesopisationResult:
            """Generate a single version with varied temperature."""
            temp = temp_variations[version_idx % len(temp_variations)]
            version_request = AesopisationRequest(
                lean_theorem_str=request.lean_theorem_str,
                context=request.context,
                max_tokens=request.max_tokens,
                temperature=temp,
                n_versions=1,
                max_retries=1,
                previous_attempts=request.previous_attempts,
                metadata={**request.metadata, "version_idx": version_idx, "temperature_used": temp}
            )
            result = self.autoformalize(version_request)
            result.metadata["version_idx"] = version_idx
            result.metadata["temperature_used"] = temp
            return result
        
        # Generate versions in parallel using ThreadPoolExecutor
        results = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(n_versions, 10)) as executor:
            futures = [executor.submit(generate_one, i) for i in range(n_versions)]
            for future in concurrent.futures.as_completed(futures):
                try:
                    results.append(future.result())
                except Exception as e:
                    results.append(AesopisationResult(
                        formal_statement="",
                        success=False,
                        error_message=str(e),
                        metadata={"model": self.model}
                    ))
        
        # Sort by version index to maintain order
        results.sort(key=lambda r: r.metadata.get("version_idx", 0))
        return results

    def autoformalize_with_retries(
        self,
        request: AesopisationRequest,
        validator: Callable[[str], Tuple[bool, str]],
    ) -> Tuple[AesopisationResult, int]:
        """Autoformalize with retry loop using error feedback.
        
        Generates a proof, validates it, and if it fails, retries with
        the error message fed back to the LLM for learning.
        
        Args:
            request: AesopisationRequest with max_retries set
            validator: Function that takes Lean code and returns (success, error_message)
            
        Returns:
            Tuple of (best result, number of attempts made)
        """
        if not self._initialized:
            self.initialize()
        
        max_retries = request.max_retries
        attempts = []
        
        # Get temperature decay factor from metadata (default 0.6)
        retry_temp_decay = request.metadata.get("retry_temp_decay", 0.6)
        
        for attempt_num in range(max_retries):
            # Decay temperature on retries for more focused output
            # First attempt uses original temp, then: 0.7 -> 0.42 -> 0.25 -> ...
            if attempt_num == 0:
                temp = request.temperature
            else:
                temp = max(0.1, request.temperature * (retry_temp_decay ** attempt_num))
            
            # Build request with previous attempts as context
            retry_request = AesopisationRequest(
                lean_theorem_str=request.lean_theorem_str,
                context=request.context,
                max_tokens=request.max_tokens,
                temperature=temp,
                n_versions=1,
                max_retries=1,
                previous_attempts=attempts if attempts else None,
                metadata={**request.metadata, "attempt_num": attempt_num, "temperature_used": temp}
            )
            
            # Generate proof
            result = self.autoformalize(retry_request)
            result.metadata["attempt_num"] = attempt_num
            result.metadata["total_attempts"] = len(attempts) + 1
            
            if not result.success:
                # LLM failed to generate, record and retry
                attempts.append({
                    "attempt": result.formal_statement or "LLM failed to generate",
                    "error": result.error_message or "Unknown LLM error"
                })
                continue
            
            # Validate the generated proof
            is_valid, error_msg = validator(result.formal_statement)
            
            if is_valid:
                result.metadata["validated"] = True
                result.metadata["validation_attempts"] = attempt_num + 1
                return result, attempt_num + 1
            
            # Record failed attempt for next retry
            attempts.append({
                "attempt": result.formal_statement,
                "error": error_msg
            })
            result.metadata["validation_error"] = error_msg
        
        # All retries exhausted, return last result with attempt history
        result.metadata["all_attempts"] = attempts
        result.metadata["validated"] = False
        return result, max_retries

    def parallel_autoformalize_with_retries(
        self,
        request: AesopisationRequest,
        validator: Callable[[str], Tuple[bool, str]],
    ) -> List[Tuple[AesopisationResult, int]]:
        """Generate multiple proof versions in parallel, each with retry capability.
        
        This is the main method for robust proof generation:
        1. Generates n_versions different proofs in parallel
        2. Each version can retry up to max_retries times with error feedback
        3. Returns all results (both successful and failed)
        
        Args:
            request: AesopisationRequest with n_versions and max_retries set
            validator: Function that takes Lean code and returns (success, error_message)
            
        Returns:
            List of (result, attempts_made) tuples for each version
        """
        if not self._initialized:
            self.initialize()
        
        n_versions = request.n_versions
        
        def process_version(version_idx: int) -> Tuple[AesopisationResult, int]:
            """Process a single version with retries."""
            # Vary temperature for diversity
            base_temp = request.temperature if request.temperature > 0 else self.default_temperature
            temp_variations = [base_temp, 0.1, 0.3, 0.5, 0.7, 0.9, 1.0, 0.2, 0.4, 0.6]
            temp = temp_variations[version_idx % len(temp_variations)]
            
            version_request = AesopisationRequest(
                lean_theorem_str=request.lean_theorem_str,
                context=request.context,
                max_tokens=request.max_tokens,
                temperature=temp,
                n_versions=1,
                max_retries=request.max_retries,
                previous_attempts=None,
                metadata={**request.metadata, "version_idx": version_idx}
            )
            
            result, attempts = self.autoformalize_with_retries(version_request, validator)
            result.metadata["version_idx"] = version_idx
            return result, attempts
        
        # Process all versions in parallel
        results = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(n_versions, 10)) as executor:
            futures = {executor.submit(process_version, i): i for i in range(n_versions)}
            for future in concurrent.futures.as_completed(futures):
                version_idx = futures[future]
                try:
                    results.append(future.result())
                except Exception as e:
                    results.append((
                        AesopisationResult(
                            formal_statement="",
                            success=False,
                            error_message=str(e),
                            metadata={"model": self.model, "version_idx": version_idx}
                        ),
                        0
                    ))
        
        # Sort by version index
        results.sort(key=lambda r: r[0].metadata.get("version_idx", 0))
        return results

    def batch_autoformalize(
        self, requests: List[AesopisationRequest]
    ) -> List[AesopisationResult]:
        """Batch autoformalize (sequential API calls)."""
        if not self._initialized:
            self.initialize()

        # Sequential processing (Nebius API doesn't support true batching)
        return [self.autoformalize(req) for req in requests]

