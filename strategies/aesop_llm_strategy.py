"""Aesop LLM strategy - uses LLM to generate aesop proofs with hints."""

from typing import Dict, Optional, Tuple, Callable
from aesop_agent.aesop_agent import AesopAgent
from aesop_agent.base import AesopisationRequest
from context.theorem_analyzer import TheoremAnalyzer
from context.context_builder import ContextBuilder
from validators.kimina_validator import KiminaValidator


class AesopLLMStrategy:
    """Strategy that uses LLM to generate aesop proofs with appropriate hints."""
    
    def __init__(
        self,
        validator: KiminaValidator,
        aesop_agent: AesopAgent,
        config: Dict
    ):
        """Initialize strategy.
        
        Args:
            validator: KiminaValidator instance
            aesop_agent: AesopAgent for LLM calls
            config: Agent configuration dict
        """
        self.validator = validator
        self.aesop_agent = aesop_agent
        self.config = config
        self.analyzer = TheoremAnalyzer()
        self.context_builder = ContextBuilder()
    
    def try_prove(
        self,
        theorem: Dict,
        imports: str,
        cleaned_content: str,
        stats: Dict
    ) -> Optional[Dict]:
        """Try to prove theorem using LLM-generated aesop proof.
        
        Args:
            theorem: Theorem dictionary
            imports: Import context string
            cleaned_content: Full cleaned Lean file content
            stats: Statistics dictionary to update
            
        Returns:
            Success dictionary if proven, None otherwise
        """
        stats['llm_attempted'] += 1
        has_simp = self.analyzer.has_simp_annotation(theorem['full_text'])
        line_number = theorem.get('line_number', 0)
        
        try:
            # Prepare theorem with fixes
            original_for_llm = theorem['full_text_renamed']
            original_for_llm = self.validator.apply_code_fixes(original_for_llm)
            
            # Create validator function
            validator_fn = self._create_validator(imports)
            
            # Build rich context
            rich_context = self._build_rich_context(
                imports,
                cleaned_content,
                line_number,
                theorem
            )
            
            # Create LLM request
            llm_request = AesopisationRequest(
                lean_theorem_str=original_for_llm,
                context=rich_context,
                temperature=self.config["temperature"],
                max_tokens=self.config["max_tokens"],
                n_versions=self.config["n_versions"],
                max_retries=self.config["max_retries"],
                metadata={"retry_temp_decay": self.config.get("retry_temp_decay", 0.6)}
            )
            
            # Generate multiple versions with retries
            all_results = self.aesop_agent.parallel_autoformalize_with_retries(
                llm_request,
                validator_fn
            )
            
            # Check for success
            successful_results = [
                (result, attempts) for result, attempts in all_results
                if result.metadata.get("validated", False)
            ]
            
            if successful_results:
                # Success!
                best_result, attempts_made = successful_results[0]
                version_idx = best_result.metadata.get("version_idx", 0)
                
                stats['llm_solved'] += 1
                
                return {
                    'name': theorem['name'],
                    'line': line_number,
                    'has_simp': has_simp,
                    'method': 'llm_assisted',
                    'success_type': 'LLM',
                    'signature': self.analyzer.extract_signature(theorem['full_text']),
                    'proof': best_result.formal_statement,
                    'original_proof': theorem['full_text_renamed'],
                    'version_idx': version_idx,
                    'attempts_made': attempts_made,
                    'total_versions_tried': len(all_results)
                }
            else:
                # Failure - return detailed info
                stats['llm_failed'] += 1
                return self._build_failure_entry(theorem, all_results, has_simp, line_number)
                
        except Exception as e:
            stats['llm_failed'] += 1
            
            failure_class = self.analyzer.classify_failure(theorem['full_text'], str(e))
            
            return {
                'name': theorem['name'],
                'line': line_number,
                'has_simp': has_simp,
                'reason': 'llm_exception',
                'failure_class': failure_class,
                'signature': self.analyzer.extract_signature(theorem['full_text']),
                'error_details': str(e),
                'llm_output': 'Exception occurred during LLM call',
                'is_failure': True
            }
    
    def _create_validator(self, imports: str) -> Callable:
        """Create a validator function for the LLM.
        
        Args:
            imports: Import context string
            
        Returns:
            Validator function
        """
        def validator(proof_code: str) -> Tuple[bool, str]:
            full_code = imports + proof_code
            full_code = self.validator.apply_code_fixes(full_code)
            is_valid, error_msg, _ = self.validator.validate_proof(full_code)
            return is_valid, error_msg
        
        return validator
    
    def _build_rich_context(
        self,
        imports: str,
        cleaned_content: str,
        line_number: int,
        theorem: Dict
    ) -> str:
        """Build rich context for LLM including lemmas and induction hints.
        
        Args:
            imports: Import context
            cleaned_content: Full cleaned file content
            line_number: Theorem line number
            theorem: Theorem dictionary
            
        Returns:
            Rich context string
        """
        # Extract previous context
        previous_content = self.context_builder.extract_previous_context(
            cleaned_content,
            line_number,
            max_chars=6000
        )
        
        # Extract and build lemma hints
        available_lemmas = self.analyzer.extract_available_lemmas(previous_content)
        lemma_hints = self.context_builder.build_lemma_hint_string(available_lemmas)
        
        # Detect induction patterns
        induction_info = self.analyzer.detect_induction_pattern(theorem['full_text'])
        induction_hint = self.context_builder.build_induction_hint(induction_info)
        
        # Combine everything
        return f"{imports}\n\n{lemma_hints}{induction_hint}\n\n-- Previous definitions and theorems from the file:\n{previous_content}"
    
    def _build_failure_entry(
        self,
        theorem: Dict,
        all_results: list,
        has_simp: bool,
        line_number: int
    ) -> Dict:
        """Build failure entry with detailed information.
        
        Args:
            theorem: Theorem dictionary
            all_results: All LLM results
            has_simp: Whether theorem has @[simp]
            line_number: Line number
            
        Returns:
            Failure entry dictionary
        """
        total_attempts = sum(a for _, a in all_results)
        
        # Get final error
        final_error_msg = ""
        if all_results:
            last_result = all_results[-1][0]
            final_error_msg = last_result.metadata.get(
                "validation_error",
                last_result.error_message or ""
            )
        
        failure_class = self.analyzer.classify_failure(theorem['full_text'], final_error_msg)
        
        # Collect version details
        all_failed_attempts = []
        for result, attempts in all_results:
            version_info = {
                'version_idx': result.metadata.get("version_idx", 0),
                'attempts': attempts,
                'final_output': result.formal_statement,
                'error': result.metadata.get("validation_error", result.error_message),
                'all_attempts': result.metadata.get("all_attempts", [])
            }
            all_failed_attempts.append(version_info)
        
        return {
            'name': theorem['name'],
            'line': line_number,
            'has_simp': has_simp,
            'reason': 'all_versions_failed',
            'failure_class': failure_class,
            'signature': self.analyzer.extract_signature(theorem['full_text']),
            'error_details': f"All {len(all_results)} LLM versions failed after {total_attempts} total attempts",
            'llm_output': all_results[0][0].formal_statement if all_results else 'No output',
            'all_versions': all_failed_attempts,
            'is_failure': True
        }
