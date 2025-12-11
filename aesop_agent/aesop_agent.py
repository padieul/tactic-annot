"""Nebius API autoformalization using OpenAI-compatible interface."""

import os
from typing import List, Optional
from openai import OpenAI

from .base import AesopAgentBase, AesopisationRequest, AesopisationResult


class AesopAgent(AesopAgentBase):
    """Nebius Studio API autoformalization (Qwen models).

    Uses Nebius Studio's OpenAI-compatible API for autoformalization.
    Requires NEBIUS_API_KEY environment variable.
    """

    DEFAULT_SYSTEM_PROMPT = """You are a Lean 4 expert. You are provided with a theorem and 
    and a proof --> I need you to create a new proof which ONLY uses aesop ... include anything
    if needed via aesop(..)"""

    def __init__(
        self,
        model: str = "Qwen/Qwen3-Coder-30B-A3B-Instruct",
        api_key: Optional[str] = None,
        base_url: str = "https://api.studio.nebius.ai/v1/",
        system_prompt: Optional[str] = None,
        default_temperature: float = 0.1,
    ):
        """Initialize Nebius API autoformalization.

        Args:
            model: Nebius model ID (default: Qwen3-Coder-30B)
            api_key: Nebius API key (default: read from NEBIUS_API_KEY env var)
            base_url: Nebius API base URL
            system_prompt: Custom system prompt (default: autoformalization prompt)
            default_temperature: Default temperature for sampling
        """
        super().__init__(model_name=f"nebius-{model.split('/')[-1]}")
        self.model = model
        self.base_url = base_url
        self.system_prompt = system_prompt or self.DEFAULT_SYSTEM_PROMPT
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
        messages = [{"role": "system", "content": self.system_prompt}]

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

        # Add main request
        messages.append({"role": "user", "content": request.natural_language})

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

    def batch_autoformalize(
        self, requests: List[AesopisationRequest]
    ) -> List[AesopisationResult]:
        """Batch autoformalize (sequential API calls)."""
        if not self._initialized:
            self.initialize()

        # Sequential processing (Nebius API doesn't support true batching)
        return [self.autoformalize(req) for req in requests]


"""
        
import Mathlib

theorem true_and_iff_extracted (p : Prop) : True ∧ p ↔ p := sorry
"""
