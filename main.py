#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Extract and validate theorems from a Lean file using Kimina."""

import os
import sys
import warnings
import logging

# Suppress warnings and reduce logging noise
warnings.filterwarnings('ignore')
logging.getLogger('httpx').setLevel(logging.WARNING)
logging.getLogger('openai').setLevel(logging.WARNING)
logging.getLogger('httpcore').setLevel(logging.WARNING)

from kimina_client import KiminaClient
from aesop_agent.aesop_agent import AesopAgent
from lean_cleaner import LeanCodeCleaner
from theorem_extractor import TheoremExtractor
from run_logger import RunLogger
from theorem_registry import TheoremRegistry
from validators.kimina_validator import KiminaValidator
from strategies.aesop_naive_strategy import AesopNaiveStrategy
from strategies.aesop_llm_strategy import AesopLLMStrategy
from theorem_validator import TheoremValidator


"""
Qwen/Qwen3-Coder-30B-A3B-Instruct
Qwen/Qwen3-30B-A3B-Thinking-2507
Qwen/Qwen3-Coder-480B-A35B-Instruct
Qwen/Qwen3-235B-A22B-Thinking-2507
"""

# Configuration
AGENT_CONFIG = {
    "model": "Qwen/Qwen3-Coder-30B-A3B-Instruct",
    "temperature": 0.7,
    "max_tokens": 4000,
    "n_versions": 5,
    "max_retries": 4,
    "retry_temp_decay": 0.0,
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
    
    # Initialize theorem registry
    print("Loading theorem registry...")
    registry = TheoremRegistry(lean_file)
    registry.print_summary()
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
    
    # Get skip list from registry
    skip_theorems = registry.get_skip_set()
    
    aesop_stats = theorem_validator.validate_theorems(
        theorems,
        skip_list=skip_theorems,
        num_to_prove=PROVE_THEOREMS_NUM
    )
    
    # Update registry with new successes
    for success in aesop_stats['all_aesop_successes']:
        registry.add_theorem(
            theorem_name=success['name'],
            proof=success['proof'],
            method=success['success_type'],
            run_id=logger.run_id
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
    logger.write_run_overview(list(skip_theorems), aesop_stats)
    logger.finalize()
    
    print(f"\n{logger.get_run_summary()}")


if __name__ == "__main__":
    main()
