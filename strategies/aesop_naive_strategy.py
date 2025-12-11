"""Aesop naive strategy - tries various aesop proof variants."""

from typing import Dict, Optional, Tuple
from context.theorem_analyzer import TheoremAnalyzer
from validators.kimina_validator import KiminaValidator


class AesopNaiveStrategy:
    """Strategy that tries different aesop variants (naive approach without LLM)."""
    
    # Aesop variants to try in order
    AESOP_VARIANTS = [
        ('by aesop', 'naive'),
        #('by simp; aesop', 'simp_then_aesop'),
        #('by simp_all; aesop', 'simp_all_then_aesop'),
        #('by aesop (config := { enableSimp := true })', 'aesop_with_simp'),
    ]
    
    def __init__(self, validator: KiminaValidator):
        """Initialize strategy.
        
        Args:
            validator: KiminaValidator instance
        """
        self.validator = validator
        self.analyzer = TheoremAnalyzer()
    
    def try_prove(
        self,
        theorem: Dict,
        imports: str,
        stats: Dict
    ) -> Optional[Dict]:
        """Try to prove theorem using aesop variants.
        
        Args:
            theorem: Theorem dictionary with 'full_text_renamed', 'name', etc.
            imports: Import context string
            stats: Statistics dictionary to update
            
        Returns:
            Success dictionary if proven, None otherwise
        """
        has_simp = self.analyzer.has_simp_annotation(theorem['full_text'])
        
        # Try each variant
        for aesop_proof, variant_name in self.AESOP_VARIANTS:
            signature = self.analyzer.extract_signature(theorem['full_text_renamed'])
            aesop_theorem_text = signature + ' := ' + aesop_proof
            aesop_code = imports + aesop_theorem_text
            
            # Apply fixes
            aesop_code = self.validator.apply_code_fixes(aesop_code)
            
            # Validate
            is_valid, error_msg, time_taken = self.validator.validate_proof(aesop_code)
            
            if is_valid:
                # Success!
                stats['aesop_solved'] += 1
                if has_simp:
                    stats['simp_aesop_solved'] += 1
                else:
                    stats['non_simp_aesop_solved'] += 1
                
                return {
                    'name': theorem['name'],
                    'line': theorem.get('line_number', 0),
                    'has_simp': has_simp,
                    'method': 'naive_aesop',
                    'success_type': 'NAIVE',
                    'variant': variant_name,
                    'signature': self.analyzer.extract_signature(theorem['full_text']),
                    'proof': aesop_theorem_text,
                    'proof_text': aesop_proof,
                    'time': time_taken
                }
        
        # All variants failed
        return None
    
    def get_failure_info(
        self,
        theorem: Dict,
        imports: str
    ) -> Tuple[str, str]:
        """Get error details from the last failed attempt.
        
        Args:
            theorem: Theorem dictionary
            imports: Import context string
            
        Returns:
            Tuple of (error_details, failure_classification)
        """
        # Try basic aesop to get error message
        signature = self.analyzer.extract_signature(theorem['full_text_renamed'])
        basic_aesop_text = signature + ' := by aesop'
        basic_aesop_code = imports + basic_aesop_text
        basic_aesop_code = self.validator.apply_code_fixes(basic_aesop_code)
        
        is_valid, error_msg, _ = self.validator.validate_proof(basic_aesop_code)
        
        failure_class = self.analyzer.classify_failure(theorem['full_text'], error_msg)
        
        return error_msg, failure_class
