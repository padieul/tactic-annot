"""Run-based logging system for aesop proof attempts."""

import os
import json
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional


class RunLogger:
    """Manages logging for a single proof run with organized directory structure."""
    
    def __init__(self, base_log_dir: str = "logs", run_name: Optional[str] = None):
        """Initialize logger for a new run.
        
        Args:
            base_log_dir: Base directory for all logs
            run_name: Optional custom name for this run. If None, uses timestamp.
        """
        self.base_log_dir = Path(base_log_dir)
        
        # Create run name from timestamp if not provided
        if run_name is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            run_name = f"run_{timestamp}"
        
        self.run_name = run_name
        self.run_dir = self.base_log_dir / run_name
        
        # Create directory structure
        self.run_dir.mkdir(parents=True, exist_ok=True)
        
        # Define log file paths
        self.overview_log = self.run_dir / "run_overview.log"
        self.successes_log = self.run_dir / "aesop_successes.log"
        self.failures_log = self.run_dir / "aesop_failures.log"
        self.metadata_json = self.run_dir / "run_metadata.json"
        
        # Initialize metadata
        self.metadata: Dict[str, Any] = {
            'run_name': run_name,
            'start_time': datetime.now().isoformat(),
            'end_time': None,
            'source_file': None,
            'config': {},
        }
        
        # Statistics tracking
        self.stats = {
            'total_theorems': 0,
            'skipped_theorems': 0,
            'attempted_theorems': 0,
            'original_validation_success': 0,
            'original_validation_failed': 0,
            'naive_aesop_success': 0,
            'llm_aesop_success': 0,
            'total_failures': 0,
            'failure_classifications': {
                'syntax_error': 0,
                'no_progress': 0,
                'partial_progress': 0,
                'fundamental': 0,
                'unknown': 0,
            },
            'aesop_variant_successes': {},
        }
    
    def set_source_file(self, filepath: str, total_theorems: int):
        """Set the source file being processed."""
        self.metadata['source_file'] = filepath
        self.stats['total_theorems'] = total_theorems
    
    def set_config(self, config: Dict[str, Any]):
        """Set the configuration used for this run."""
        self.metadata['config'] = config
    
    def write_run_overview(self, skipped_theorems: List[str], aesop_stats: Dict[str, Any]):
        """Write comprehensive run overview.
        
        Args:
            skipped_theorems: List of theorem names that were skipped
            aesop_stats: Full statistics dictionary from the run
        """
        with open(self.overview_log, 'w', encoding='utf-8') as f:
            f.write("=" * 80 + "\n")
            f.write(f"AESOP PROOF RUN OVERVIEW: {self.run_name}\n")
            f.write("=" * 80 + "\n")
            f.write(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
            f.write(f"Source file: {self.metadata.get('source_file', 'N/A')}\n\n")
            
            # Configuration
            f.write("CONFIGURATION:\n")
            f.write("-" * 80 + "\n")
            config = self.metadata.get('config', {})
            for key, value in config.items():
                f.write(f"  {key}: {value}\n")
            f.write("\n")
            
            # Overall statistics
            f.write("OVERALL STATISTICS:\n")
            f.write("-" * 80 + "\n")
            f.write(f"Total theorems in source: {self.stats['total_theorems']}\n")
            f.write(f"Theorems skipped (already solved): {len(skipped_theorems)}\n")
            f.write(f"Theorems attempted in this run: {self.stats['attempted_theorems']}\n")
            f.write(f"Original proof validation success: {self.stats['original_validation_success']}\n")
            f.write(f"Original proof validation failed: {self.stats['original_validation_failed']}\n\n")
            
            # Skipped theorems list
            if skipped_theorems:
                f.write("SKIPPED THEOREMS (already solved in previous runs):\n")
                f.write("-" * 80 + "\n")
                for i, thm in enumerate(skipped_theorems, 1):
                    f.write(f"  {i}. {thm}\n")
                f.write("\n")
            
            # Aesop success breakdown
            f.write("AESOP SUCCESS BREAKDOWN:\n")
            f.write("-" * 80 + "\n")
            f.write(f"Total aesop successes: {self.stats['naive_aesop_success'] + self.stats['llm_aesop_success']}\n")
            f.write(f"  - Naive aesop (no LLM): {self.stats['naive_aesop_success']}\n")
            
            # Breakdown by variant
            if self.stats.get('aesop_variant_successes'):
                f.write("    Breakdown by variant:\n")
                for variant, count in self.stats['aesop_variant_successes'].items():
                    f.write(f"      • {variant}: {count}\n")
            
            f.write(f"  - LLM-assisted aesop: {self.stats['llm_aesop_success']}\n\n")
            
            # Failure breakdown
            f.write("AESOP FAILURE BREAKDOWN:\n")
            f.write("-" * 80 + "\n")
            f.write(f"Total failures: {self.stats['total_failures']}\n\n")
            
            if self.stats['total_failures'] > 0:
                f.write("Failure Classification:\n")
                fc = self.stats['failure_classifications']
                total_classified = sum(fc.values())
                
                if fc['syntax_error'] > 0:
                    pct = fc['syntax_error'] / self.stats['total_failures'] * 100
                    f.write(f"  - Syntax errors (FIXABLE): {fc['syntax_error']} ({pct:.1f}%)\n")
                
                if fc['partial_progress'] > 0:
                    pct = fc['partial_progress'] / self.stats['total_failures'] * 100
                    f.write(f"  - Partial progress (NEEDS MORE HINTS): {fc['partial_progress']} ({pct:.1f}%)\n")
                
                if fc['no_progress'] > 0:
                    pct = fc['no_progress'] / self.stats['total_failures'] * 100
                    f.write(f"  - No progress (UNKNOWN): {fc['no_progress']} ({pct:.1f}%)\n")
                
                if fc['fundamental'] > 0:
                    pct = fc['fundamental'] / self.stats['total_failures'] * 100
                    f.write(f"  - Fundamental limitations (NEEDS INDUCTION/OTHER): {fc['fundamental']} ({pct:.1f}%)\n")
                
                if fc['unknown'] > 0:
                    pct = fc['unknown'] / self.stats['total_failures'] * 100
                    f.write(f"  - Unknown: {fc['unknown']} ({pct:.1f}%)\n")
                
                f.write("\n")
            
            # Success rate
            if self.stats['attempted_theorems'] > 0:
                success_count = self.stats['naive_aesop_success'] + self.stats['llm_aesop_success']
                success_rate = success_count / self.stats['attempted_theorems'] * 100
                f.write("SUCCESS RATE:\n")
                f.write("-" * 80 + "\n")
                f.write(f"{success_count}/{self.stats['attempted_theorems']} theorems proven ")
                f.write(f"({success_rate:.1f}% success rate)\n\n")
            
            # Summary
            f.write("REMAINING WORK:\n")
            f.write("-" * 80 + "\n")
            remaining = self.stats['total_failures']
            f.write(f"Theorems still to solve: {remaining}\n")
            if remaining > 0:
                fixable = fc['syntax_error'] + fc['partial_progress']
                f.write(f"  - Potentially fixable with better prompts/hints: {fixable}\n")
                f.write(f"  - May need different approach (induction, etc.): {fc['fundamental']}\n")
            
            f.write("\n" + "=" * 80 + "\n")
    
    def write_successes(self, successes: List[Dict[str, Any]]):
        """Write aesop successes log."""
        with open(self.successes_log, 'w', encoding='utf-8') as f:
            f.write(f"AESOP SUCCESSES - RUN: {self.run_name}\n")
            f.write(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
            f.write(f"{'='*80}\n\n")
            f.write(f"Total successes in this run: {len(successes)}\n\n")
            
            for idx, success in enumerate(successes, 1):
                success_type = success.get('success_type', 'UNKNOWN')
                variant = success.get('variant', 'aesop')
                
                f.write(f"{'='*80}\n")
                f.write(f"SUCCESS #{idx}: {success['name']} [{success_type}]\n")
                f.write(f"{'='*80}\n")
                f.write(f"Line number: {success['line']}\n")
                f.write(f"Has @[simp]: {success['has_simp']}\n")
                f.write(f"Method: {success['method']}\n")
                
                if success_type == 'NAIVE':
                    f.write(f"Variant: {variant}\n")
                
                f.write(f"Context: {success.get('context', 'N/A')}\n")
                
                # Add version and retry info for LLM-assisted proofs
                if success['method'] == 'llm_assisted':
                    if 'version_idx' in success:
                        f.write(f"LLM Version: {success['version_idx'] + 1}\n")
                    if 'attempts_made' in success:
                        f.write(f"LLM Attempts: {success['attempts_made']}\n")
                
                f.write(f"\nTheorem signature:\n")
                f.write(f"{'-'*80}\n")
                f.write(f"{success['signature']}\n")
                f.write(f"{'-'*80}\n")
                
                f.write(f"\nSuccessful proof:\n")
                f.write(f"{'-'*80}\n")
                f.write(f"{success['proof']}\n")
                f.write(f"{'-'*80}\n")
                
                if success['method'] == 'llm_assisted' and 'original_proof' in success:
                    f.write(f"\nOriginal proof (for reference):\n")
                    f.write(f"{'-'*80}\n")
                    f.write(f"{success['original_proof']}\n")
                    f.write(f"{'-'*80}\n")
                
                f.write(f"\n\n")
    
    def write_failures(self, failures: List[Dict[str, Any]], classifications: Dict[str, List[Dict]]):
        """Write aesop failures log."""
        with open(self.failures_log, 'w', encoding='utf-8') as f:
            f.write(f"AESOP FAILURES - RUN: {self.run_name}\n")
            f.write(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
            f.write(f"{'='*80}\n\n")
            f.write(f"Total failures in this run: {len(failures)}\n\n")
            
            # Summary by classification
            if classifications:
                f.write(f"FAILURE BREAKDOWN:\n")
                f.write(f"  - Syntax errors (FIXABLE): {len(classifications.get('syntax_error', []))}\n")
                f.write(f"  - No progress (UNKNOWN): {len(classifications.get('no_progress', []))}\n")
                f.write(f"  - Partial progress (NEEDS HINTS): {len(classifications.get('partial_progress', []))}\n")
                f.write(f"  - Fundamental (NOT AESOP-SOLVABLE): {len(classifications.get('fundamental', []))}\n")
                f.write(f"  - Unknown: {len(classifications.get('unknown', []))}\n\n")
            
            # Group failures by classification
            classification_order = ['syntax_error', 'partial_progress', 'no_progress', 'fundamental', 'unknown']
            
            for classification_name in classification_order:
                class_failures = [f for f in failures if f.get('failure_class', 'unknown').startswith(classification_name)]
                if not class_failures:
                    continue
                    
                f.write(f"\n{'='*80}\n")
                f.write(f"CATEGORY: {classification_name.upper()}\n")
                f.write(f"{'='*80}\n\n")
                
                for idx, failure in enumerate(class_failures, 1):
                    f.write(f"{'-'*80}\n")
                    f.write(f"FAILURE: {failure['name']}\n")
                    f.write(f"{'-'*80}\n")
                    f.write(f"Line number: {failure['line']}\n")
                    f.write(f"Has @[simp]: {failure['has_simp']}\n")
                    f.write(f"Failure reason: {failure['reason']}\n")
                    f.write(f"Classification: {failure.get('failure_class', 'unknown')}\n")
                    f.write(f"Context: {failure.get('context', 'N/A')}\n")
                    f.write(f"\nOriginal theorem signature:\n")
                    f.write(f"{'-'*80}\n")
                    f.write(f"{failure['signature']}\n")
                    f.write(f"{'-'*80}\n")
                    
                    # Add LLM output if available
                    if 'llm_output' in failure and failure['llm_output']:
                        f.write(f"\nLLM suggested proof (final):\n")
                        f.write(f"{'-'*80}\n")
                        f.write(f"{failure['llm_output']}\n")
                        f.write(f"{'-'*80}\n")
                    
                    if 'error_details' in failure and failure['error_details']:
                        f.write(f"\nError details:\n")
                        f.write(f"{'-'*80}\n")
                        f.write(f"{failure['error_details']}\n")
                        f.write(f"{'-'*80}\n")
                    
                    # Add detailed version information if available
                    if 'all_versions' in failure and failure['all_versions']:
                        f.write(f"\n{'~'*80}\n")
                        f.write(f"DETAILED VERSION ATTEMPTS ({len(failure['all_versions'])} versions):\n")
                        f.write(f"{'~'*80}\n")
                        for ver_info in failure['all_versions']:
                            f.write(f"\n  Version {ver_info['version_idx'] + 1} ({ver_info['attempts']} attempts):\n")
                            output_preview = ver_info['final_output'][:200] + "..." if ver_info['final_output'] and len(ver_info['final_output']) > 200 else ver_info['final_output']
                            f.write(f"  Final output: {output_preview}\n")
                            f.write(f"\n  Final error: {ver_info['error']}\n")
                            
                            # Show retry history
                            if ver_info.get('all_attempts'):
                                f.write(f"  Retry history:\n")
                                for retry_idx, attempt_info in enumerate(ver_info['all_attempts'], 1):
                                    f.write(f"    Retry {retry_idx}:\n")
                                    attempt_preview = attempt_info['attempt'][:150] + "..." if len(attempt_info['attempt']) > 150 else attempt_info['attempt']
                                    f.write(f"      Attempt: {attempt_preview}\n")
                                    error_preview = attempt_info['error'][:200] + "..." if len(attempt_info['error']) > 200 else attempt_info['error']
                                    f.write(f"      Error: {error_preview}\n")
                    
                    f.write(f"\n")
    
    def update_stats(self, aesop_stats: Dict[str, Any]):
        """Update internal statistics from aesop_stats dictionary."""
        self.stats['attempted_theorems'] = aesop_stats.get('total_attempted', 0)
        self.stats['naive_aesop_success'] = aesop_stats.get('aesop_solved', 0)
        self.stats['llm_aesop_success'] = aesop_stats.get('llm_solved', 0)
        self.stats['total_failures'] = aesop_stats.get('llm_failed', 0)
        self.stats['skipped_theorems'] = aesop_stats.get('skipped_theorems', 0)
        
        # Update failure classifications counts
        fc = aesop_stats.get('failure_classifications', {})
        for key in self.stats['failure_classifications']:
            self.stats['failure_classifications'][key] = len(fc.get(key, []))
        
        # Track variant successes
        for success in aesop_stats.get('all_aesop_successes', []):
            if success.get('success_type') == 'NAIVE':
                variant = success.get('variant', 'unknown')
                self.stats['aesop_variant_successes'][variant] = \
                    self.stats['aesop_variant_successes'].get(variant, 0) + 1
    
    def finalize(self):
        """Finalize the run and write metadata."""
        self.metadata['end_time'] = datetime.now().isoformat()
        self.metadata['statistics'] = self.stats
        
        with open(self.metadata_json, 'w', encoding='utf-8') as f:
            json.dump(self.metadata, f, indent=2)
    
    def get_run_summary(self) -> str:
        """Get a brief summary of the run for console output."""
        success_count = self.stats['naive_aesop_success'] + self.stats['llm_aesop_success']
        attempted = self.stats['attempted_theorems']
        
        if attempted > 0:
            success_rate = success_count / attempted * 100
            return (f"Run: {self.run_name} | "
                   f"{success_count}/{attempted} proven ({success_rate:.1f}%) | "
                   f"Logs: {self.run_dir}")
        return f"Run: {self.run_name} | No theorems attempted | Logs: {self.run_dir}"
