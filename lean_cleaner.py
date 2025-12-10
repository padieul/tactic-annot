# lean_cleaner.py
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Clean corrupted Unicode in Lean 4 files."""

import re


class LeanCodeCleaner:
    """
    Handles cleaning of corrupted Unicode characters in Lean 4 source files.
    
    This class provides methods to replace corrupted characters (typically '?')
    with their proper Lean 4 equivalents, including subscripts, arrows, Greek letters,
    and mathematical symbols.
    """
    
    # Lookup table for character replacements
    REPLACEMENTS = {
        # Subscripts and special notation
        '₂': '₂',
        
        # Arrow types (ring homomorphisms)
        '→+*': '→+*',
        '→*': '→*',
        '→+': '→+',
        
        # Greek letters
        'ι': 'ι',
        'φ': 'φ',
        'ψ': 'ψ',
        
        # Number types
        'ℕ': 'Nat',
        'ℤ': 'Int',
        'ℝ': 'Real',
        'ℚ': 'Rat',
        
        # Logical symbols
        '∀': '∀',
        '∃': '∃',
        '∧': '∧',
        '∨': '∨',
        '¬': '¬',
        '↔': '↔',
        '→': '→',
        '←': '←',
        '⊢': '⊢',
        
        # Other mathematical symbols
        '∑': '∑',
        '∏': '∏',
        '∈': '∈',
        '∣': '∣',
        '≠': '≠',
        '≤': '≤',
        '≥': '≥',
    }
    
    def __init__(self):
        """Initialize the cleaner with default settings."""
        pass
    
    def clean(self, content: str) -> str:
        """
        Clean corrupted Lean code by replacing broken Unicode with proper Lean 4 syntax.
        
        Args:
            content: Raw Lean source code with potential Unicode corruption
            
        Returns:
            Cleaned Lean source code with proper Unicode characters
        """
        cleaned = content
        
        # Apply replacements in specific order to avoid conflicts
        cleaned = self._fix_eval_subscripts(cleaned)
        cleaned = self._fix_ring_homomorphism_arrows(cleaned)
        cleaned = self._fix_number_types(cleaned)
        cleaned = self._fix_type_variables(cleaned)
        cleaned = self._fix_number_annotations(cleaned)
        cleaned = self._fix_finset_contexts(cleaned)
        cleaned = self._fix_polynomial_variables(cleaned)
        cleaned = self._fix_polynomial_references(cleaned)
        cleaned = self._fix_function_arguments(cleaned)
        cleaned = self._fix_tactic_arrows(cleaned) 
        cleaned = self._fix_implications(cleaned)
        
        return cleaned
    
    def _fix_eval_subscripts(self, content: str) -> str:
        """Replace eval? with eval₂."""
        return re.sub(r'eval\?', 'eval₂', content)
    
    def _fix_ring_homomorphism_arrows(self, content: str) -> str:
        """Replace ring homomorphism arrow notation."""
        content = re.sub(r'\?\+\*', '→+*', content)
        content = re.sub(r'\?\+', '→+', content)
        content = re.sub(r'\?\*', '→*', content)
        return content
    
    def _fix_number_types(self, content: str) -> str:
        """Replace blackboard bold number type symbols."""
        content = content.replace('ℕ', 'Nat')
        content = content.replace('ℤ', 'Int')
        content = content.replace('ℝ', 'Real')
        content = content.replace('ℚ', 'Rat')
        return content
    
    def _fix_type_variables(self, content: str) -> str:
        """Fix type variable declarations."""
        content = re.sub(r'\{\?\s*:\s*Type\s+y\}', '{ι : Type y}', content)
        content = re.sub(r'variable\s*\{\?\s*:\s*Type', 'variable {ι : Type', content)
        return content
    
    def _fix_tactic_arrows(self, content: str) -> str:
        """Fix left arrows (←) in tactic arguments that appear as ?."""
        # Pattern: rw [? becomes rw [←
        content = re.sub(r'\[(\s*)\?(\s+)', r'[←\2', content)
        return content
    
    def _fix_number_annotations(self, content: str) -> str:
        """Fix Nat type annotations."""
        content = re.sub(r':\s*\?}', ': Nat}', content)
        content = re.sub(r':\s*\?]', ': Nat]', content)
        content = re.sub(r'\(n\s*:\s*\?\)', '(n : Nat)', content)
        content = re.sub(r'\{n\s*:\s*\?\}', '{n : Nat}', content)
        content = re.sub(r'\{k\s*:\s*\?\}', '{k : Nat}', content)
        return content
    
    def _fix_finset_contexts(self, content: str) -> str:
        """Fix Finset type contexts."""
        return re.sub(r'Finset\s+\?', 'Finset ι', content)
    
    def _fix_polynomial_variables(self, content: str) -> str:
        """Fix polynomial variable type declarations: {? ? : R[X]} -> {φ ψ : R[X]}."""
        return re.sub(r'\{\?\s+\?\s*:\s*R\[X\]\}', '{φ ψ : R[X]}', content)
    
    def _fix_polynomial_references(self, content: str) -> str:
        """Fix polynomial variable references in equations: ? = ? -> φ = ψ."""
        return re.sub(r'\?\s*=\s*\?', 'φ = ψ', content)
    
    def _fix_function_arguments(self, content: str) -> str:
        """Fix standalone ? that refers to φ in function calls."""
        return re.sub(r'(eval₂\s+\w+\s+\w+)\s+\?', r'\1 φ', content)
    
    def _fix_implications(self, content: str) -> str:
        """Fix remaining ? characters that represent → (implication arrows)."""
        return re.sub(r'(\w+)\s+\?(\s)', r'\1 →\2', content)
    
    def get_stats(self, original: str, cleaned: str) -> dict:
        """
        Get statistics about the cleaning operation.
        
        Args:
            original: Original content before cleaning
            cleaned: Cleaned content after cleaning
            
        Returns:
            Dictionary with statistics about changes made
        """
        return {
            'original_length': len(original),
            'cleaned_length': len(cleaned),
            'question_marks_remaining': cleaned.count('?'),
            'eval2_count': cleaned.count('eval₂'),
            'arrow_operators': cleaned.count('→+*') + cleaned.count('→+') + cleaned.count('→*'),
            'left_arrows': cleaned.count('←'),
        }