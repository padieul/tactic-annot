"""Theorem validator - orchestrates validation of theorems using multiple strategies."""

from typing import Dict, List, Set
from context.theorem_analyzer import TheoremAnalyzer
from context.context_builder import ContextBuilder
from validators.kimina_validator import KiminaValidator
from strategies.aesop_naive_strategy import AesopNaiveStrategy
from strategies.aesop_llm_strategy import AesopLLMStrategy


class TheoremValidator:
    """Orchestrates validation of theorems using original proof, naive aesop, and LLM strategies."""
    
    def __init__(
        self,
        validator: KiminaValidator,
        naive_strategy: AesopNaiveStrategy,
        llm_strategy: AesopLLMStrategy,
        cleaned_content: str
    ):
        """Initialize the validator.
        
        Args:
            validator: KiminaValidator instance
            naive_strategy: AesopNaiveStrategy instance
            llm_strategy: AesopLLMStrategy instance
            cleaned_content: Full cleaned Lean file content
        """
        self.validator = validator
        self.naive_strategy = naive_strategy
        self.llm_strategy = llm_strategy
        self.cleaned_content = cleaned_content
        self.analyzer = TheoremAnalyzer()
        self.context_builder = ContextBuilder()
    
    def validate_theorems(
        self,
        theorems: List[Dict],
        skip_list: Set[str],
        num_to_prove: int = None
    ) -> Dict:
        """Validate a list of theorems.
        
        Args:
            theorems: List of theorem dictionaries
            skip_list: Set of theorem names to skip
            num_to_prove: Number of theorems to validate (None = all)
            
        Returns:
            Statistics dictionary with results
        """
        # Initialize statistics
        stats = self._init_stats()
        
        # Determine how many to prove
        if num_to_prove is None:
            num_to_prove = len(theorems)
        
        theorems_to_prove = theorems[:num_to_prove]
        
        # Process theorems with simple output
        total = len(theorems_to_prove)
        for idx, theorem in enumerate(theorems_to_prove):
            result = self._validate_single_theorem(theorem, idx, skip_list, stats)
            
            # Print simple one-line status
            status = "✓ SOLVED" if result else "✗ NOT SOLVED"
            print(f"[{idx+1}/{total}] {theorem['name']}: {status}")
        
        return stats
    
    def _validate_single_theorem(
        self,
        theorem: Dict,
        idx: int,
        skip_list: Set[str],
        stats: Dict
    ) -> bool:
        """Validate a single theorem through all strategies.
        
        Args:
            theorem: Theorem dictionary
            idx: Index in the list
            skip_list: Set of theorem names to skip
            stats: Statistics dictionary to update
            
        Returns:
            True if successful (original or aesop), False otherwise
        """
        theorem_name = theorem['name']
        line_number = theorem.get('line_number', 0)
        has_simp = self.analyzer.has_simp_annotation(theorem['full_text'])
        
        # Track @[simp] annotations
        if has_simp:
            stats['simp_total'] += 1
        
        # Skip if in skip list
        if theorem_name in skip_list:
            stats['skipped_theorems'] += 1
            return True
        
        # Detect context
        context_key = self.context_builder.detect_context(theorem, line_number)
        imports = self.context_builder.get_imports(context_key)
        
        # Step 1: Validate with original proof
        original_valid = self._validate_original(theorem, imports, stats)
        
        if not original_valid:
            return False
        
        # Step 2: Try naive aesop variants
        stats['total_attempted'] += 1
        
        naive_result = self.naive_strategy.try_prove(theorem, imports, stats)
        
        if naive_result:
            # Success with naive aesop!
            stats['aesop_solved_theorems'].append(naive_result)
            stats['all_aesop_successes'].append({
                **naive_result,
                'context': context_key
            })
            return True
        
        # Naive aesop failed
        stats['aesop_failed'] += 1
        
        # Get error details
        error_details, failure_class = self.naive_strategy.get_failure_info(theorem, imports)
        
        # Track @[simp] failures
        if has_simp:
            stats['simp_aesop_failed'] += 1
            stats['simp_not_solved_by_aesop'].append({
                'name': theorem_name,
                'line': line_number,
                'reason': 'all_variants_failed'
            })
        
        # Step 3: Try LLM-assisted proof
        llm_result = self.llm_strategy.try_prove(
            theorem,
            imports,
            self.cleaned_content,
            stats
        )
        
        if llm_result and not llm_result.get('is_failure', False):
            # Success with LLM!
            stats['llm_solved_theorems'].append(llm_result)
            stats['all_aesop_successes'].append({
                **llm_result,
                'context': context_key
            })
            return True
        
        # Complete failure - add to failures list
        if llm_result and llm_result.get('is_failure', False):
            failure_entry = {
                **llm_result,
                'context': context_key
            }
            # Add original aesop error context
            if 'error_details' in failure_entry:
                failure_entry['error_details'] = f"Original aesop error:\n{error_details.strip()}\n\n{failure_entry['error_details']}"
            else:
                failure_entry['error_details'] = f"Original aesop error:\n{error_details.strip()}"
            
            stats['aesop_failed_theorems'].append(failure_entry)
            
            # Track in classifications
            class_key = failure_entry['failure_class'].split(':')[0]
            if class_key in stats['failure_classifications']:
                stats['failure_classifications'][class_key].append(failure_entry)
            else:
                stats['failure_classifications']['unknown'].append(failure_entry)
        
        return False
    
    def _validate_original(
        self,
        theorem: Dict,
        imports: str,
        stats: Dict
    ) -> bool:
        """Validate theorem with original proof.
        
        Args:
            theorem: Theorem dictionary
            imports: Import context
            stats: Statistics to update
            
        Returns:
            True if original proof is valid
        """
        full_code = imports + theorem['full_text_renamed']
        full_code = self.validator.apply_code_fixes(full_code)
        
        is_valid, error_msg, time_taken = self.validator.validate_proof(full_code)
        
        return is_valid
    
    def _init_stats(self) -> Dict:
        """Initialize statistics dictionary.
        
        Returns:
            Empty stats dictionary
        """
        return {
            'skipped_theorems': 0,
            'total_attempted': 0,
            'aesop_solved': 0,
            'aesop_failed': 0,
            'llm_attempted': 0,
            'llm_solved': 0,
            'llm_failed': 0,
            'simp_total': 0,
            'simp_aesop_solved': 0,
            'simp_aesop_failed': 0,
            'non_simp_aesop_solved': 0,
            'aesop_solved_theorems': [],
            'llm_solved_theorems': [],
            'all_aesop_successes': [],
            'aesop_failed_theorems': [],
            'simp_not_solved_by_aesop': [],
            'failure_classifications': {
                'syntax_error': [],
                'no_progress': [],
                'partial_progress': [],
                'fundamental': [],
                'unknown': []
            }
        }
