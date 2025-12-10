# main.py
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Extract and validate theorems from a Lean file using Kimina."""

from kimina_client import KiminaClient
from lean_cleaner import LeanCodeCleaner
from theorem_extractor import TheoremExtractor
from datetime import datetime

# Configuration constants
PRINT_THEOREMS_NUM = 124  # Number of theorems to print
PROVE_THEOREMS_NUM = 124   # Number of theorems to validate
AESOP_FAILURES_LOG = 'aesop_failures.log'


# Define different import contexts based on Lean file sections
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


def detect_theorem_context(theorem: dict, line_number: int) -> str:
    """
    Detect which import context a theorem needs based on its line number and content.
    
    Args:
        theorem: Dictionary containing theorem information
        line_number: Line number in the original file
        
    Returns:
        Key for IMPORT_CONTEXTS dictionary
    """
    theorem_text = theorem['full_text']
    
    # Line-based heuristics (adjusted for section boundaries)
    if line_number < 210:
        # Early theorems use Semiring S with eval₂
        return 'semiring_s'
    elif 210 <= line_number < 256:
        # Section Eval₂ with CommSemiring S
        return 'commsemiring_s'
    elif 256 <= line_number < 384:
        # Section Eval with just R
        return 'eval_r'
    elif 384 <= line_number < 494:
        # Section Comp (still in Eval context)
        return 'eval_r'
    elif 494 <= line_number < 606:
        # Section Map - needs special Semiring S context
        return 'map_section'
    elif 606 <= line_number < 711:
        # CommSemiring section
        return 'commsemiring_r'
    elif 711 <= line_number < 737:
        # NoZeroDivisors subsection
        return 'commsemiring_nozerodiv'
    elif line_number >= 737:
        # Ring section
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
    
    # Default to the most general case
    return 'semiring_s'


def extract_theorem_signature(theorem_text: str) -> str:
    """
    Extract just the theorem signature (everything before := or :=).
    
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


def check_has_simp_annotation(theorem_text: str) -> bool:
    """
    Check if theorem has @[simp] annotation.
    
    Args:
        theorem_text: Full theorem text including any preceding annotations
        
    Returns:
        True if @[simp] annotation is present
    """
    return '@[simp]' in theorem_text or '@[aesop norm simp]' in theorem_text


def create_aesop_version(theorem_text: str) -> str:
    """
    Create a version of the theorem with proof replaced by 'by aesop'.
    
    Args:
        theorem_text: Original theorem text with proof
        
    Returns:
        Theorem with proof replaced by 'by aesop'
    """
    # Find the := and replace everything after it with 'by aesop'
    if ':=' in theorem_text:
        signature = extract_theorem_signature(theorem_text)
        return signature + ' := by aesop'
    return theorem_text


def write_aesop_failures_log(failures: list, log_file: str):
    """
    Write detailed information about aesop failures to a log file.
    
    Args:
        failures: List of failure dictionaries
        log_file: Path to the log file
    """
    with open(log_file, 'w', encoding='utf-8') as f:
        f.write(f"AESOP FAILURES LOG\n")
        f.write(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"{'='*80}\n\n")
        f.write(f"Total failures: {len(failures)}\n\n")
        
        for idx, failure in enumerate(failures, 1):
            f.write(f"{'='*80}\n")
            f.write(f"FAILURE #{idx}: {failure['name']}\n")
            f.write(f"{'='*80}\n")
            f.write(f"Line number: {failure['line']}\n")
            f.write(f"Has @[simp]: {failure['has_simp']}\n")
            f.write(f"Failure reason: {failure['reason']}\n")
            f.write(f"Context: {failure.get('context', 'N/A')}\n")
            f.write(f"\nOriginal theorem signature:\n")
            f.write(f"{'-'*80}\n")
            f.write(f"{failure['signature']}\n")
            f.write(f"{'-'*80}\n")
            
            if 'error_details' in failure and failure['error_details']:
                f.write(f"\nError details:\n")
                f.write(f"{'-'*80}\n")
                f.write(f"{failure['error_details']}\n")
                f.write(f"{'-'*80}\n")
            
            f.write(f"\n\n")


def main():
    # Read the Lean file
    lean_file = 'data/full_defs_new.lean'
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
        has_simp = check_has_simp_annotation(thm['full_text'])
        simp_marker = " [@simp]" if has_simp else ""
        print(f"  {i}. {thm['name']} -> {thm['renamed']} (line {thm['line_number']}){simp_marker}")
    print()
    
    # Initialize Kimina client
    print("Connecting to Kimina server...")
    client = KiminaClient(
        api_url="http://localhost:8000",
        http_timeout=120,
        n_retries=3
    )
    
    # Validate first PROVE_THEOREMS_NUM theorems
    num_to_prove = min(PROVE_THEOREMS_NUM, len(theorems))
    print(f"Validating first {num_to_prove} theorem(s)\n")
    
    success_count = 0
    failed_theorems = []
    context_usage = {}
    aesop_stats = {
        'total_attempted': 0,
        'aesop_solved': 0,
        'aesop_failed': 0,
        'simp_total': 0,
        'simp_aesop_solved': 0,
        'simp_aesop_failed': 0,
        'non_simp_aesop_solved': 0,
        'aesop_solved_theorems': [],
        'aesop_failed_theorems': [],
        'simp_not_solved_by_aesop': []
    }
    
    for idx in range(num_to_prove):
        theorem = theorems[idx]
        line_number = theorem['line_number']
        has_simp = check_has_simp_annotation(theorem['full_text'])
        
        if has_simp:
            aesop_stats['simp_total'] += 1
        
        # Detect the appropriate context for this theorem
        context_key = detect_theorem_context(theorem, line_number)
        context_usage[context_key] = context_usage.get(context_key, 0) + 1
        imports = IMPORT_CONTEXTS[context_key]
        
        # Always show basic info
        simp_marker = " [@simp]" if has_simp else ""
        print(f"[{idx + 1}/{num_to_prove}] {theorem['name']}{simp_marker} -> {theorem['renamed']} ", end='', flush=True)
        
        # Use the RENAMED version to avoid conflicts with Mathlib
        full_code = imports + theorem['full_text_renamed']
        
        # Fix induction_on' syntax: 'add' -> 'h_add', 'monomial' -> 'h_monomial'
        full_code = full_code.replace('| add ', '| h_add ')
        full_code = full_code.replace('| monomial ', '| h_monomial ')
        
        # Fix namespace issue: map_dvd needs _root_ prefix in eval₂RingHom context
        full_code = full_code.replace(
            'map_dvd (eval₂RingHom',
            '_root_.map_dvd (eval₂RingHom'
        )
        
        # Step 1: Validate with original proof
        original_valid = False
        try:
            response = client.check(full_code, timeout=60)
            result = response.results[0]
            analysis = result.analyze()
            
            if analysis.status == "valid":
                print(f"✓ ({result.time:.3f}s) ", end='', flush=True)
                success_count += 1
                original_valid = True
            else:
                print(f"✗ ({result.time:.3f}s) ", end='', flush=True)
                failed_theorems.append({
                    'index': idx + 1,
                    'name': theorem['name'],
                    'line': line_number,
                    'context': context_key,
                    'status': analysis.status,
                    'has_simp': has_simp
                })
                    
        except Exception as e:
            print(f"✗ EXCEPTION ", end='', flush=True)
            failed_theorems.append({
                'index': idx + 1,
                'name': theorem['name'],
                'line': line_number,
                'context': context_key,
                'status': 'exception',
                'has_simp': has_simp
            })
        
        # Step 2: Try with aesop (only if original validation succeeded)
        if original_valid:
            aesop_stats['total_attempted'] += 1
            
            # Create aesop version
            aesop_theorem_text = create_aesop_version(theorem['full_text_renamed'])
            aesop_code = imports + aesop_theorem_text
            
            # Apply same fixes
            aesop_code = aesop_code.replace('| add ', '| h_add ')
            aesop_code = aesop_code.replace('| monomial ', '| h_monomial ')
            aesop_code = aesop_code.replace(
                'map_dvd (eval₂RingHom',
                '_root_.map_dvd (eval₂RingHom'
            )
            
            try:
                response = client.check(aesop_code, timeout=60)
                result = response.results[0]
                analysis = result.analyze()
                
                if analysis.status == "valid":
                    print(f"| aesop ✓ ({result.time:.3f}s)")
                    aesop_stats['aesop_solved'] += 1
                    aesop_stats['aesop_solved_theorems'].append({
                        'name': theorem['name'],
                        'line': line_number,
                        'has_simp': has_simp
                    })
                    if has_simp:
                        aesop_stats['simp_aesop_solved'] += 1
                    else:
                        aesop_stats['non_simp_aesop_solved'] += 1
                else:
                    print(f"| aesop ✗ ({result.time:.3f}s)")
                    aesop_stats['aesop_failed'] += 1
                    
                    # Collect error details
                    error_details = ""
                    if result.response and result.response.get("messages"):
                        for msg in result.response["messages"]:
                            if msg["severity"] == "error":
                                error_details += f"{msg['data']}\n"
                    
                    failure_entry = {
                        'name': theorem['name'],
                        'line': line_number,
                        'has_simp': has_simp,
                        'reason': analysis.status,
                        'context': context_key,
                        'signature': extract_theorem_signature(theorem['full_text']),
                        'error_details': error_details.strip()
                    }
                    
                    aesop_stats['aesop_failed_theorems'].append(failure_entry)
                    
                    # Track @[simp] theorems that aesop couldn't solve
                    if has_simp:
                        aesop_stats['simp_aesop_failed'] += 1
                        aesop_stats['simp_not_solved_by_aesop'].append({
                            'name': theorem['name'],
                            'line': line_number,
                            'reason': analysis.status
                        })
            except Exception as e:
                print(f"| aesop ✗ (exception)")
                aesop_stats['aesop_failed'] += 1
                
                failure_entry = {
                    'name': theorem['name'],
                    'line': line_number,
                    'has_simp': has_simp,
                    'reason': 'exception',
                    'context': context_key,
                    'signature': extract_theorem_signature(theorem['full_text']),
                    'error_details': str(e)
                }
                
                aesop_stats['aesop_failed_theorems'].append(failure_entry)
                
                # Track @[simp] theorems that aesop couldn't solve
                if has_simp:
                    aesop_stats['simp_aesop_failed'] += 1
                    aesop_stats['simp_not_solved_by_aesop'].append({
                        'name': theorem['name'],
                        'line': line_number,
                        'reason': 'exception'
                    })
        else:
            print()  # New line if we didn't test aesop
    
    # Write aesop failures to log file
    if aesop_stats['aesop_failed_theorems']:
        print(f"\nWriting aesop failures to {AESOP_FAILURES_LOG}...")
        write_aesop_failures_log(aesop_stats['aesop_failed_theorems'], AESOP_FAILURES_LOG)
        print(f"Log file written successfully.")
    
    # Summary
    print(f"\n{'='*60}")
    print(f"VALIDATION SUMMARY")
    print(f"{'='*60}")
    print(f"Total theorems validated: {num_to_prove}")
    print(f"Successful: {success_count} ({success_count/num_to_prove*100:.1f}%)")
    print(f"Failed: {len(failed_theorems)} ({len(failed_theorems)/num_to_prove*100:.1f}%)")
    print(f"\nContext usage: {context_usage}")
    
    print(f"\n{'='*60}")
    print(f"AESOP STATISTICS")
    print(f"{'='*60}")
    print(f"Theorems tested with aesop: {aesop_stats['total_attempted']}")
    print(f"Aesop solved: {aesop_stats['aesop_solved']} ({aesop_stats['aesop_solved']/aesop_stats['total_attempted']*100:.1f}% of attempted)" if aesop_stats['total_attempted'] > 0 else "Aesop solved: 0")
    print(f"Aesop failed: {aesop_stats['aesop_failed']}")
    if aesop_stats['aesop_failed'] > 0:
        print(f"  (Details written to {AESOP_FAILURES_LOG})")
    print(f"\n@[simp] Annotation Analysis:")
    print(f"  Total @[simp] theorems: {aesop_stats['simp_total']}")
    print(f"  @[simp] solved by aesop: {aesop_stats['simp_aesop_solved']} ({aesop_stats['simp_aesop_solved']/aesop_stats['simp_total']*100:.1f}%)" if aesop_stats['simp_total'] > 0 else "  @[simp] solved by aesop: 0")
    print(f"  @[simp] NOT solved by aesop: {aesop_stats['simp_aesop_failed']} ({aesop_stats['simp_aesop_failed']/aesop_stats['simp_total']*100:.1f}%)" if aesop_stats['simp_total'] > 0 else "  @[simp] NOT solved by aesop: 0")
    print(f"  Non-@[simp] solved by aesop: {aesop_stats['non_simp_aesop_solved']}")
    
    if aesop_stats['aesop_solved_theorems']:
        print(f"\n{'='*60}")
        print(f"THEOREMS SOLVED BY AESOP ({len(aesop_stats['aesop_solved_theorems'])}):")
        print(f"{'='*60}")
        for thm in aesop_stats['aesop_solved_theorems']:
            simp_marker = " [@simp]" if thm['has_simp'] else ""
            print(f"  {thm['name']} (line {thm['line']}){simp_marker}")
    
    if aesop_stats['simp_not_solved_by_aesop']:
        print(f"\n{'='*60}")
        print(f"@[simp] THEOREMS NOT SOLVED BY AESOP ({len(aesop_stats['simp_not_solved_by_aesop'])}):")
        print(f"{'='*60}")
        for thm in aesop_stats['simp_not_solved_by_aesop']:
            print(f"  {thm['name']} (line {thm['line']}) - reason: {thm['reason']}")
    
    if failed_theorems:
        print(f"\n{'='*60}")
        print(f"FAILED THEOREMS:")
        print(f"{'='*60}")
        for failure in failed_theorems:
            simp_marker = " [@simp]" if failure['has_simp'] else ""
            print(f"  [{failure['index']}] {failure['name']} (line {failure['line']}, context: {failure['context']}, status: {failure['status']}){simp_marker}")
    
    print(f"{'='*60}")


if __name__ == "__main__":
    main()