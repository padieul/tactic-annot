#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Extract and validate theorems from a Lean file using Kimina."""

from kimina_client import KiminaClient
from aesop_agent.aesop_agent import AesopAgent
from lean_cleaner import LeanCodeCleaner
from theorem_extractor import TheoremExtractor
from run_logger import RunLogger
from validators.kimina_validator import KiminaValidator
from strategies.aesop_naive_strategy import AesopNaiveStrategy
from strategies.aesop_llm_strategy import AesopLLMStrategy
from theorem_validator import TheoremValidator


# Configuration
AGENT_CONFIG = {
    "model": "Qwen/Qwen3-Coder-480B-A35B-Instruct",
    "temperature": 0.7,
    "max_tokens": 2048,
    "n_versions": 3,
    "max_retries": 2,
    "retry_temp_decay": 0.6,
}

# Theorems to skip (already solved)
SKIP_THEOREMS = {
    # Naive aesop successes (82 theorems)
    'eval₂_congr', 'eval₂_zero', 'eval₂_C', 'eval₂_X', 'eval₂_monomial', 'eval₂_X_pow',
    'eval₂_add', 'eval₂_one', 'eval₂_natCast', 'eval₂_ofNat', 'eval₂_mul_X', 'eval₂_X_mul',
    'eval₂_mul', 'eval₂_mul_eq_zero_of_left', 'eval₂_mul_eq_zero_of_right', 'coe_eval₂RingHom',
    'eval₂_id', 'eval₂_at_apply', 'eval₂_at_one', 'eval₂_at_natCast', 'eval₂_at_ofNat',
    'eval_C', 'eval_natCast', 'eval_ofNat', 'eval_X', 'eval_monomial', 'eval_zero',
    'eval_add', 'eval_one', 'eval_C_mul', 'eval_natCast_mul', 'eval_mul_X', 'eval_mul_X_pow',
    'IsRoot', 'not_isRoot_C', 'comp_X', 'X_comp', 'comp_C', 'C_comp', 'natCast_comp',
    'ofNat_comp', 'comp_zero', 'zero_comp', 'comp_one', 'one_comp', 'add_comp',
    'monomial_comp', 'mul_X_comp', 'X_pow_comp', 'mul_X_pow_comp', 'C_mul_comp',
    'natCast_mul_comp', 'mul_comp', 'pow_comp', 'map_C', 'map_X', 'map_monomial',
    'coe_mapRingHom', 'mapRingHom_comp_C', 'eval_mul', 'coe_evalRingHom', 'eval_pow',
    'eval_X_pow', 'eval_comp', 'isRoot_comp', 'coe_compRingHom', 'coe_compRingHom_apply',
    'root_mul_left_of_isRoot', 'root_mul_right_of_isRoot', 'eval_geom_sum', 'root_mul',
    'root_or_root_of_root_mul', 'eval_intCast', 'eval₂_neg', 'eval₂_sub', 'eval_neg',
    'eval_sub', 'neg_comp', 'sub_comp', 'intCast_comp', 'eval₂_at_intCast',
    
    # LLM-assisted aesop successes (13 theorems)
    #'eval₂_eq_sum', 'eval₂_ofFinsupp', 'eval₂_mul_noncomm', 'eval₂_list_prod_noncomm',
    #'eval_eq_sum', 'eval_listSum', 'eval_surjective', 'comp_eq_sum_left', 'comp_assoc',
    #'eval₂_eq_eval_map', 'eval_map', 'isRoot_prod', 'root_X_sub_C',
}

PRINT_THEOREMS_NUM = 124
PROVE_THEOREMS_NUM = 124


def main():
    """Main entry point."""
    # Initialize logger
    logger = RunLogger()
    
    # Read and clean Lean file
    lean_file = 'data/full_defs_new.lean'
    print(f"Reading {lean_file}...")
    
    with open(lean_file, 'r', encoding='utf-8', errors="replace") as f:
        content = f.read()
    
    print(f"Loaded {len(content)} characters")
    print("Cleaning corrupted Unicode...")
    
    cleaner = LeanCodeCleaner()
    cleaned_content = cleaner.clean(content)
    
    stats = cleaner.get_stats(content, cleaned_content)
    print(f"Cleaned (eval₂ count: {stats['eval2_count']}, "
          f"remaining '?': {stats['question_marks_remaining']})\n")
    
    # Extract theorems
    print("Extracting theorems...")
    extractor = TheoremExtractor(rename_suffix="_test")
    theorems = extractor.extract(cleaned_content)
    print(f"Found {len(theorems)} theorems\n")
    
    if not theorems:
        print("No theorems found!")
        return
    
    # Configure logger
    logger.set_source_file(lean_file, len(theorems))
    logger.set_config(AGENT_CONFIG)
    
    # Show first theorems
    num_to_print = min(PRINT_THEOREMS_NUM, len(theorems))
    print(f"First {num_to_print} theorems:")
    for i, thm in enumerate(theorems[:num_to_print], 1):
        from context.theorem_analyzer import TheoremAnalyzer
        has_simp = TheoremAnalyzer.has_simp_annotation(thm['full_text'])
        simp_marker = " [@simp]" if has_simp else ""
        print(f"  {i}. {thm['name']} -> {thm['renamed']} (line {thm['line_number']}){simp_marker}")
    print()
    
    # Initialize Kimina client
    print("Connecting to Kimina server...")
    kimina_client = KiminaClient(
        api_url="http://localhost:8000",
        http_timeout=120,
    )
    print("Connected to Kimina")
    
    # Initialize aesop agent
    print("Initializing Aesop agent...")
    aesop_agent = AesopAgent(
        model=AGENT_CONFIG["model"],
        default_temperature=AGENT_CONFIG["temperature"]
    )
    aesop_agent.initialize()
    
    # Create validator and strategies
    validator = KiminaValidator(kimina_client)
    naive_strategy = AesopNaiveStrategy(validator)
    llm_strategy = AesopLLMStrategy(validator, aesop_agent, AGENT_CONFIG)
    
    # Create orchestrator
    theorem_validator = TheoremValidator(
        validator=validator,
        naive_strategy=naive_strategy,
        llm_strategy=llm_strategy,
        cleaned_content=cleaned_content
    )
    
    # Validate theorems
    print(f"\nValidating {PROVE_THEOREMS_NUM} theorems...\n")
    aesop_stats = theorem_validator.validate_theorems(
        theorems,
        skip_list=SKIP_THEOREMS,
        num_to_prove=PROVE_THEOREMS_NUM
    )
    
    # Write logs
    logger.update_stats(aesop_stats)
    
    if aesop_stats['all_aesop_successes']:
        print(f"\nWriting aesop successes...")
        logger.write_successes(aesop_stats['all_aesop_successes'])
    
    if aesop_stats['aesop_failed_theorems']:
        print(f"Writing aesop failures...")
        logger.write_failures(
            aesop_stats['aesop_failed_theorems'],
            aesop_stats['failure_classifications']
        )
    
    # Finalize
    logger.write_run_overview(list(SKIP_THEOREMS), aesop_stats)
    logger.finalize()
    
    print(f"\n{logger.get_run_summary()}")


if __name__ == "__main__":
    main()
