# theorem_extractor.py
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Extract theorem declarations from Lean 4 source files."""

import re
from typing import List, Dict


class TheoremExtractor:
    """
    Extracts theorem and lemma declarations from Lean 4 source code.
    
    This class can identify theorem/lemma declarations, extract their full text,
    and optionally rename them to avoid naming conflicts.
    """
    
    # Keywords that indicate the start of a theorem/lemma
    DECLARATION_KEYWORDS = ('theorem ', 'lemma ')
    
    # Keywords that indicate we should stop collecting lines
    STOP_KEYWORDS = (
        'theorem ', 'lemma ', 'def ', 'instance ', 'axiom ', 'example ',
        'end', 'section ', 'namespace ', '@[', '/-', '/--', 'protected '
    )
    
    def __init__(self, rename_suffix: str = "_test"):
        """
        Initialize the extractor.
        
        Args:
            rename_suffix: Suffix to append to theorem names to avoid conflicts
        """
        self.rename_suffix = rename_suffix
    
    def extract(self, lean_content: str) -> List[Dict[str, any]]:
        """
        Extract all theorems from Lean source code.
        
        Args:
            lean_content: Lean 4 source code as a string
            
        Returns:
            List of dictionaries containing theorem information:
                - name: Original theorem name
                - renamed: New theorem name with suffix
                - full_text: Original theorem text
                - full_text_renamed: Theorem text with renamed declaration
                - line_number: Starting line number (1-indexed)
        """
        theorems = []
        lines = lean_content.split('\n')
        
        i = 0
        while i < len(lines):
            line = lines[i].strip()
            
            if self._is_theorem_start(line):
                theorem = self._extract_theorem(lines, i)
                if theorem:
                    theorems.append(theorem)
                    i = theorem['_end_line']
                else:
                    i += 1
            else:
                i += 1
        
        return theorems
    
    def _is_theorem_start(self, line: str) -> bool:
        """Check if a line starts a theorem declaration."""
        return any(line.startswith(keyword) for keyword in self.DECLARATION_KEYWORDS)
    
    def _collect_preceding_annotations(self, lines: List[str], theorem_idx: int) -> List[str]:
        """
        Collect any @[...] annotations that appear before the theorem.
        
        Args:
            lines: All lines of the file
            theorem_idx: Index where theorem declaration starts
            
        Returns:
            List of lines containing annotations (in order)
        """
        annotation_lines = []
        j = theorem_idx - 1
        
        # Look backwards for annotations
        while j >= 0:
            line = lines[j].strip()
            
            # Stop if we hit an empty line or non-annotation content
            if line == '':
                j -= 1
                continue
            
            # If it's an attribute annotation, include it
            if line.startswith('@['):
                annotation_lines.insert(0, lines[j])
                j -= 1
            else:
                # Stop if we hit something that's not an annotation
                break
        
        return annotation_lines
    
    def _extract_theorem(self, lines: List[str], start_idx: int) -> Dict[str, any]:
        """
        Extract a single theorem starting at the given line.
        
        Args:
            lines: All lines of the file
            start_idx: Index where theorem starts
            
        Returns:
            Dictionary with theorem information or None if extraction failed
        """
        line = lines[start_idx].strip()
        
        # Extract theorem name
        name_match = re.search(r'(?:theorem|lemma)\s+(\w+)', line)
        if not name_match:
            return None
        
        name = name_match.group(1)
        
        # Collect any preceding annotations
        annotation_lines = self._collect_preceding_annotations(lines, start_idx)
        
        # Start with annotations, then the theorem declaration
        theorem_lines = annotation_lines + [lines[start_idx]]
        
        # Collect lines until we find the end
        j = start_idx + 1
        while j < len(lines):
            next_line = lines[j].strip()
            
            # Stop if we hit a new declaration or attribute
            if self._should_stop(next_line, j, start_idx):
                break
            
            theorem_lines.append(lines[j])
            j += 1
        
        full_text = '\n'.join(theorem_lines).strip()
        
        # Create renamed version
        new_name = name + self.rename_suffix
        full_text_renamed = self._rename_theorem(full_text, name, new_name)
        
        return {
            'name': name,
            'renamed': new_name,
            'full_text': full_text,
            'full_text_renamed': full_text_renamed,
            'line_number': start_idx + 1,  # Still report the theorem declaration line
            '_end_line': j  # Internal use for iteration
        }
    
    def _should_stop(self, line: str, current_idx: int, start_idx: int) -> bool:
        """Determine if we should stop collecting lines for current theorem."""
        if current_idx <= start_idx:
            return False
        return any(line.startswith(keyword) for keyword in self.STOP_KEYWORDS)
    
    def _rename_theorem(self, text: str, old_name: str, new_name: str) -> str:
        """
        Rename a theorem in its text.
        
        Args:
            text: Original theorem text
            old_name: Original theorem name
            new_name: New theorem name
            
        Returns:
            Text with renamed theorem
        """
        return re.sub(
            r'((?:theorem|lemma)\s+)' + re.escape(old_name) + r'\b',
            r'\1' + new_name,
            text,
            count=1
        )
    
    def get_summary(self, theorems: List[Dict[str, any]]) -> Dict[str, any]:
        """
        Get a summary of extracted theorems.
        
        Args:
            theorems: List of extracted theorems
            
        Returns:
            Dictionary with summary statistics
        """
        return {
            'total_count': len(theorems),
            'theorem_names': [t['name'] for t in theorems],
            'average_length': sum(len(t['full_text']) for t in theorems) / len(theorems) if theorems else 0,
        }