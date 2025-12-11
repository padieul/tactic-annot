"""Context builder - creates Lean import contexts and lemma hints."""

from typing import Dict, List


class ContextBuilder:
    """Builds Lean import contexts and extracts lemma hints."""
    
    # Import contexts for different sections of the Lean file
    IMPORT_CONTEXTS = {
        'semiring_s': """import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.GroupWithZero.Associated

open Finset AddMonoidAlgebra
open Polynomial

namespace Polynomial

variable {R : Type*} {S : Type*} {T : Type*} {ι : Type*} {a b : R} {m n : Nat}

section Semiring
variable [Semiring R] {p q r : R[X]}
section
variable [Semiring S]
variable (f : R →+* S) (x : S)
variable [Semiring T]

""",
        
        'commsemiring_s': """import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.GroupWithZero.Associated

open Finset AddMonoidAlgebra
open Polynomial

namespace Polynomial

variable {R : Type*} {S : Type*} {T : Type*} {ι : Type*} {a b : R} {m n : Nat}

section Semiring
variable [Semiring R] {p q r : R[X]}
section
variable [CommSemiring S]
variable (f : R →+* S) (x : S)
variable [Semiring T]

""",
        
        'eval_r': """import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.GroupWithZero.Associated

open Finset AddMonoidAlgebra
open Polynomial

namespace Polynomial

variable {R : Type*} {S : Type*} {T : Type*} {ι : Type*} {a b : R} {m n : Nat}

section Semiring
variable [Semiring R] {p q r : R[X]}

section Eval
variable {x : R}

""",

        'map_section': """import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.GroupWithZero.Associated

open Finset AddMonoidAlgebra
open Polynomial

namespace Polynomial

variable {R : Type*} {S : Type*} {T : Type*} {ι : Type*} {a b : R} {m n : Nat}

section Semiring
variable [Semiring R] {p q r : R[X]}

section Map
variable [Semiring S]
variable (f : R →+* S)

""",

        'commsemiring_r': """import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.GroupWithZero.Associated

open Finset AddMonoidAlgebra
open Polynomial

namespace Polynomial

variable {R : Type*} {S : Type*} {T : Type*} {ι : Type*} {a b : R} {m n : Nat}

section CommSemiring
variable [CommSemiring R] {p q r : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

""",

        'commsemiring_nozerodiv': """import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.GroupWithZero.Associated

open Finset AddMonoidAlgebra
open Polynomial

namespace Polynomial

variable {R : Type*} {S : Type*} {T : Type*} {ι : Type*} {a b : R} {m n : Nat}

section CommSemiring
variable [CommSemiring R] {p q r : R[X]} {x : R} [CommSemiring S] (f : R →+* S)
variable [NoZeroDivisors R]

""",

        'ring': """import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.GroupWithZero.Associated

open Finset AddMonoidAlgebra
open Polynomial

namespace Polynomial

variable {R : Type*} {S : Type*} {T : Type*} {ι : Type*} {a b : R} {m n : Nat}

section Ring
variable [Ring R] {p q r : R[X]}

""",
    }
    
    @staticmethod
    def detect_context(theorem: Dict, line_number: int) -> str:
        """Detect which import context a theorem needs.
        
        Args:
            theorem: Dictionary containing theorem information
            line_number: Line number in the original file
            
        Returns:
            Key for IMPORT_CONTEXTS dictionary
        """
        theorem_text = theorem['full_text']
        
        # Line-based heuristics (adjusted for section boundaries)
        if line_number < 210:
            return 'semiring_s'
        elif 210 <= line_number < 256:
            return 'commsemiring_s'
        elif 256 <= line_number < 384:
            return 'eval_r'
        elif 384 <= line_number < 494:
            return 'eval_r'
        elif 494 <= line_number < 606:
            return 'map_section'
        elif 606 <= line_number < 711:
            return 'commsemiring_r'
        elif 711 <= line_number < 737:
            return 'commsemiring_nozerodiv'
        elif line_number >= 737:
            return 'ring'
        
        # Content-based heuristics as fallback
        if 'eval₂' in theorem_text and 'CommSemiring S' in theorem_text:
            return 'commsemiring_s'
        elif 'eval₂' in theorem_text and 'f :' in theorem_text:
            return 'semiring_s'
        elif '.map ' in theorem_text or 'map f' in theorem_text:
            return 'map_section'
        elif 'NoZeroDivisors' in theorem_text or 'root_mul' in theorem_text:
            return 'commsemiring_nozerodiv'
        elif '.eval ' in theorem_text and 'CommSemiring R' in theorem_text:
            return 'commsemiring_r'
        elif '.eval ' in theorem_text:
            return 'eval_r'
        elif 'Ring R' in theorem_text:
            return 'ring'
        
        return 'semiring_s'
    
    @staticmethod
    def get_imports(context_key: str) -> str:
        """Get import context for a given key.
        
        Args:
            context_key: Key from IMPORT_CONTEXTS
            
        Returns:
            Import string
        """
        return ContextBuilder.IMPORT_CONTEXTS.get(context_key, ContextBuilder.IMPORT_CONTEXTS['semiring_s'])
    
    @staticmethod
    def build_lemma_hint_string(lemma_names: List[str], max_lemmas: int = 50) -> str:
        """Build a hint string listing available lemmas.
        
        Args:
            lemma_names: List of lemma/theorem names
            max_lemmas: Maximum number to include
            
        Returns:
            Formatted string for LLM prompt
        """
        if not lemma_names:
            return ""
        
        limited_lemmas = lemma_names[:max_lemmas]
        lemma_list = ", ".join(limited_lemmas)
        
        hint = f"\nAVAILABLE LEMMAS (from earlier in file - you can use these as aesop hints):\n{lemma_list}\n"
        if len(lemma_names) > max_lemmas:
            hint += f"\n(... and {len(lemma_names) - max_lemmas} more)\n"
        
        return hint
    
    @staticmethod
    def extract_previous_context(cleaned_content: str, theorem_line_number: int, max_chars: int = 8000) -> str:
        """Extract previous theorems/lemmas from the file as context.
        
        Args:
            cleaned_content: The cleaned Lean file content
            theorem_line_number: Line number of current theorem
            max_chars: Maximum characters to extract
            
        Returns:
            Previous context string
        """
        lines = cleaned_content.split('\n')
        
        # Get all lines before the current theorem
        previous_lines = lines[:theorem_line_number - 1]
        
        # Extract theorem/lemma/def blocks (reverse to get most recent first)
        context_blocks = []
        current_block = []
        in_block = False
        
        for line in reversed(previous_lines):
            # Start of a theorem/lemma/def (we're going backwards)
            if any(line.strip().startswith(kw) for kw in ['theorem ', 'lemma ', 'def ']):
                in_block = True
                current_block.insert(0, line)
                # Save this block
                block_text = '\n'.join(current_block)
                context_blocks.append(block_text)
                current_block = []
                in_block = False
            elif in_block:
                current_block.insert(0, line)
        
        # Reverse to get chronological order and join
        context_blocks.reverse()
        full_context = '\n\n'.join(context_blocks)
        
        # Truncate if too long
        if len(full_context) > max_chars:
            full_context = full_context[-max_chars:]
            # Try to start at a theorem boundary
            theorem_start = full_context.find('\ntheorem ')
            if theorem_start > 0:
                full_context = full_context[theorem_start + 1:]
        
        return full_context
    
    @staticmethod
    def build_induction_hint(induction_info: Dict) -> str:
        """Build an induction hint string based on detected patterns.
        
        Args:
            induction_info: Dict from TheoremAnalyzer.detect_induction_pattern
            
        Returns:
            Hint string for LLM
        """
        if not induction_info['needs_induction']:
            return ""
        
        var = induction_info['induction_var']
        coll_type = induction_info['collection_type']
        
        if induction_info['induction_type'] == 'list':
            return f"\nIMPORTANT: This theorem involves {coll_type}. Consider using:\n  induction {var} with | nil => aesop | cons h t ih => aesop (add norm ih)\nOr more concisely: induction {var} <;> aesop"
        elif induction_info['induction_type'] == 'finset':
            return f"\nIMPORTANT: This theorem involves {coll_type}. Consider using:\n  induction {var} using Finset.induction_on with | empty => aesop | insert a s ha ih => aesop (add norm ih)"
        elif induction_info['induction_type'] == 'multiset':
            return f"\nIMPORTANT: This theorem involves {coll_type}. Consider using:\n  induction {var} using Multiset.induction_on with | empty => aesop | cons a s ih => aesop (add norm ih)"
        
        return ""
