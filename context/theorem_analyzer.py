"""Theorem analyzer - extracts information and detects patterns in theorems."""

import re
from typing import Dict, List


class TheoremAnalyzer:
    """Analyzes theorems to extract signatures, detect patterns, and classify content."""
    
    @staticmethod
    def extract_signature(theorem_text: str) -> str:
        """Extract just the theorem signature (everything before :=).
        
        Args:
            theorem_text: Full theorem text
            
        Returns:
            Just the signature part
        """
        lines = theorem_text.split('\n')
        signature_lines = []
        
        for line in lines:
            if ':=' in line:
                # Include the part before :=
                before_assign = line.split(':=')[0]
                signature_lines.append(before_assign)
                break
            else:
                signature_lines.append(line)
        
        return '\n'.join(signature_lines).strip()
    
    @staticmethod
    def has_simp_annotation(theorem_text: str) -> bool:
        """Check if theorem has @[simp] annotation.
        
        Args:
            theorem_text: Full theorem text including any preceding annotations
            
        Returns:
            True if @[simp] annotation is present
        """
        return '@[simp]' in theorem_text or '@[aesop norm simp]' in theorem_text
    
    @staticmethod
    def detect_induction_pattern(theorem_text: str) -> Dict:
        """Detect if a theorem needs induction based on patterns.
        
        Looks for:
        - List.sum, List.prod patterns
        - Finset.sum, Finset.prod patterns  
        - Multiset.sum, Multiset.prod patterns
        
        Args:
            theorem_text: Full theorem text
            
        Returns:
            Dict with keys:
                - needs_induction: bool
                - induction_type: 'list', 'finset', 'multiset', or None
                - collection_type: str describing the collection
                - induction_var: str variable name to induct on
        """
        # Check for List patterns
        list_sum_match = re.search(r'\((\w+)\s*:\s*List[^)]*\).*\.sum', theorem_text)
        list_prod_match = re.search(r'\((\w+)\s*:\s*List[^)]*\).*\.prod', theorem_text)
        
        if list_sum_match:
            return {
                'needs_induction': True,
                'induction_type': 'list',
                'collection_type': 'List with .sum',
                'induction_var': list_sum_match.group(1)
            }
        
        if list_prod_match:
            return {
                'needs_induction': True,
                'induction_type': 'list',
                'collection_type': 'List with .prod',
                'induction_var': list_prod_match.group(1)
            }
        
        # Check for Finset patterns
        finset_sum_match = re.search(r'\((\w+)\s*:\s*Finset[^)]*\).*\.sum', theorem_text)
        finset_prod_match = re.search(r'\((\w+)\s*:\s*Finset[^)]*\).*\.prod', theorem_text)
        
        if finset_sum_match:
            return {
                'needs_induction': True,
                'induction_type': 'finset',
                'collection_type': 'Finset with .sum',
                'induction_var': finset_sum_match.group(1)
            }
        
        if finset_prod_match:
            return {
                'needs_induction': True,
                'induction_type': 'finset',
                'collection_type': 'Finset with .prod',
                'induction_var': finset_prod_match.group(1)
            }
        
        # Check for Multiset patterns
        multiset_sum_match = re.search(r'\((\w+)\s*:\s*Multiset[^)]*\).*\.sum', theorem_text)
        multiset_prod_match = re.search(r'\((\w+)\s*:\s*Multiset[^)]*\).*\.prod', theorem_text)
        
        if multiset_sum_match:
            return {
                'needs_induction': True,
                'induction_type': 'multiset',
                'collection_type': 'Multiset with .sum',
                'induction_var': multiset_sum_match.group(1)
            }
        
        if multiset_prod_match:
            return {
                'needs_induction': True,
                'induction_type': 'multiset',
                'collection_type': 'Multiset with .prod',
                'induction_var': multiset_prod_match.group(1)
            }
        
        # No induction pattern detected
        return {
            'needs_induction': False,
            'induction_type': None,
            'collection_type': None,
            'induction_var': None
        }
    
    @staticmethod
    def classify_failure(theorem_text: str, error_msg: str) -> str:
        """Classify why an aesop proof failed.
        
        Args:
            theorem_text: The theorem text
            error_msg: Error message from validation
            
        Returns:
            Classification string with category prefix
        """
        error_lower = error_msg.lower()
        
        # Syntax errors - fixable by correcting aesop syntax
        if any(phrase in error_lower for phrase in [
            'phase not specified',
            'unexpected token',
            'expected',
            'invalid',
            'syntax error',
            'unable to interpret'
        ]):
            return 'syntax_error: Aesop syntax error - fixable'
        
        # No progress - aesop didn't find anything
        if any(phrase in error_lower for phrase in [
            'failed to prove',
            'unsolved goals',
            'tactic failed'
        ]) and 'made no progress' in error_lower:
            return 'no_progress: Aesop made no progress - might need different hints'
        
        # Partial progress - aesop did something but got stuck
        if any(phrase in error_lower for phrase in [
            'unsolved goals',
            'failed to prove'
        ]):
            return 'partial_progress: Aesop made partial progress - needs more lemma hints'
        
        # Fundamental issues - theorem might not be aesop-solvable
        if any(phrase in error_lower for phrase in [
            'timeout',
            'maximum recursion depth',
            'type mismatch',
            'failed to unify'
        ]):
            return 'fundamental: Likely not aesop-solvable without significant changes'
        
        # Unknown
        return 'unknown: Unclassified failure type'
    
    @staticmethod
    def extract_available_lemmas(previous_content: str) -> List[str]:
        """Extract theorem and lemma names from previous content.
        
        Args:
            previous_content: Previous theorems/lemmas from the file
            
        Returns:
            List of lemma/theorem names
        """
        lemma_pattern = r'(?:theorem|lemma|def)\s+(\w+)'
        matches = re.findall(lemma_pattern, previous_content)
        return list(set(matches))  # Remove duplicates
