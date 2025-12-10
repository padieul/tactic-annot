# multi_theorem_test.py
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Extract and validate theorems from a Lean file using Kimina."""

from kimina_client import KiminaClient
from lean_cleaner import LeanCodeCleaner
from theorem_extractor import TheoremExtractor

# Configuration constants
PRINT_THEOREMS_NUM = 124  # Number of theorems to print
PROVE_THEOREMS_NUM = 20   # Number of theorems to validate


def main():
    # Read the Lean file
    lean_file = 'data/full_defs.lean'
    print(f"Reading {lean_file}...")
    
    with open(lean_file, 'r', encoding='utf-8', errors="replace") as f:
        content = f.read()
    
    print(f"Loaded {len(content)} characters")
    
    # Clean the corrupted Lean code
    print("Cleaning corrupted Unicode...")
    cleaner = LeanCodeCleaner()
    cleaned_content = cleaner.clean(content)
    
    # Show cleaning stats
    stats = cleaner.get_stats(content, cleaned_content)
    print(f"Cleaned (eval₂ count: {stats['eval2_count']}, "
          f"remaining '?': {stats['question_marks_remaining']})\n")
    
    # Extract theorems with renamed versions
    print("Extracting theorems...")
    extractor = TheoremExtractor(rename_suffix="_test")
    theorems = extractor.extract(cleaned_content)
    print(f"Found {len(theorems)} theorems\n")
    
    if not theorems:
        print("No theorems found!")
        return
    
    # Show first PRINT_THEOREMS_NUM theorem names
    num_to_print = min(PRINT_THEOREMS_NUM, len(theorems))
    print(f"First {num_to_print} theorems:")
    for i, thm in enumerate(theorems[:num_to_print], 1):
        print(f"  {i}. {thm['name']} -> {thm['renamed']} (line {thm['line_number']})")
    print()
    
    # Initialize Kimina client
    print("Connecting to Kimina server...")
    client = KiminaClient(
        api_url="http://localhost:8000",
        http_timeout=120,
        n_retries=3
    )
    
    # Prepare imports for validation
    imports = """import Mathlib.Algebra.Group.Nat.Hom
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

"""
    
    # Validate first PROVE_THEOREMS_NUM theorems
    num_to_prove = min(PROVE_THEOREMS_NUM, len(theorems))
    print(f"Validating first {num_to_prove} theorem(s)\n")
    
    success_count = 0
    for idx in range(num_to_prove):
        theorem = theorems[idx]
        print(f"\n{'='*60}")
        print(f"Theorem {idx + 1}/{num_to_prove}: {theorem['name']} -> {theorem['renamed']}")
        print(f"{'='*60}")
        preview = theorem['full_text_renamed'][:150]
        print(preview + "..." if len(theorem['full_text_renamed']) > 150 else theorem['full_text_renamed'])
        print()
        
        # Use the RENAMED version to avoid conflicts with Mathlib
        full_code = imports + theorem['full_text_renamed']
        
        try:
            response = client.check(full_code, timeout=60)
            result = response.results[0]
            analysis = result.analyze()
            
            print(f"Status: {analysis.status}")
            print(f"Time: {result.time:.3f}s")
            
            if analysis.status == "valid":
                print("✓ Theorem is valid!")
                success_count += 1
            elif analysis.status == "sorry":
                print("⚠ Theorem contains sorry")
                if result.response and result.response.get("sorries"):
                    for sorry in result.response["sorries"]:
                        print(f"\n  Goal at sorry:\n{sorry['goal']}")
            elif analysis.status == "lean_error":
                print("✗ Lean error:")
                if result.response and result.response.get("messages"):
                    for msg in result.response["messages"]:
                        if msg["severity"] == "error":
                            print(f"\n  {msg['data']}")
            else:
                print(f"✗ Error: {analysis.status}")
                if result.error:
                    print(f"  {result.error}")
                    
        except Exception as e:
            print(f"✗ Error validating theorem: {e}")
    
    print(f"\n{'='*60}")
    print(f"Completed validation: {success_count}/{num_to_prove} theorems valid")
    print(f"{'='*60}")


if __name__ == "__main__":
    main()