"""Theorem registry - tracks successfully aesop-ized theorems."""

import json
from pathlib import Path
from typing import Dict, List, Optional, Set
from datetime import datetime


class TheoremRegistry:
    """Manages a registry of successfully aesop-ized theorems for a Lean file."""
    
    def __init__(self, lean_file_path: str, registry_dir: str = "logs"):
        """Initialize the registry.
        
        Args:
            lean_file_path: Path to the Lean file (e.g., 'data/full_defs_new.lean')
            registry_dir: Directory where registry files are stored
        """
        self.lean_file_path = lean_file_path
        self.registry_dir = Path(registry_dir)
        self.registry_dir.mkdir(parents=True, exist_ok=True)
        
        # Create registry filename based on Lean file name
        lean_filename = Path(lean_file_path).stem
        self.registry_file = self.registry_dir / f"{lean_filename}_aesop_registry.json"
        
        # Load existing registry
        self.registry = self._load_registry()
    
    def _load_registry(self) -> Dict:
        """Load registry from file or create new one.
        
        Returns:
            Registry dictionary
        """
        if self.registry_file.exists():
            with open(self.registry_file, 'r', encoding='utf-8') as f:
                return json.load(f)
        else:
            return {
                'lean_file': self.lean_file_path,
                'created': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                'last_updated': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                'theorems': {}
            }
    
    def _save_registry(self):
        """Save registry to file."""
        self.registry['last_updated'] = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        with open(self.registry_file, 'w', encoding='utf-8') as f:
            json.dump(self.registry, f, indent=2, ensure_ascii=False)
    
    def add_theorem(
        self,
        theorem_name: str,
        proof: str,
        method: str,
        run_id: str,
        signature: str = "",
        variant: str = None,
        metadata: Dict = None
    ):
        """Add a successfully aesop-ized theorem to the registry.
        
        Args:
            theorem_name: Name of the theorem
            proof: The successful aesop proof
            method: 'naive' or 'llm'
            run_id: Run ID when this proof was found
            signature: Theorem signature (optional)
            variant: Aesop variant used (for naive method)
            metadata: Additional metadata
        """
        entry = {
            'proof': proof,
            'method': method,
            'run_id': run_id,
            'timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            'signature': signature
        }
        
        if variant:
            entry['variant'] = variant
        
        if metadata:
            entry['metadata'] = metadata
        
        self.registry['theorems'][theorem_name] = entry
        self._save_registry()
    
    def add_batch(self, successes: List[Dict], run_id: str):
        """Add a batch of successful theorems from a run.
        
        Args:
            successes: List of success dictionaries
            run_id: Run ID
        """
        for success in successes:
            method = 'naive' if success.get('success_type') == 'NAIVE' else 'llm'
            self.add_theorem(
                theorem_name=success['name'],
                proof=success.get('proof', ''),
                method=method,
                run_id=run_id,
                signature=success.get('signature', ''),
                variant=success.get('variant'),
                metadata={
                    'line': success.get('line'),
                    'has_simp': success.get('has_simp'),
                    'context': success.get('context')
                }
            )
    
    def has_theorem(self, theorem_name: str) -> bool:
        """Check if a theorem is already in the registry.
        
        Args:
            theorem_name: Name of the theorem
            
        Returns:
            True if theorem is in registry
        """
        return theorem_name in self.registry['theorems']
    
    def get_theorem(self, theorem_name: str) -> Optional[Dict]:
        """Get theorem entry from registry.
        
        Args:
            theorem_name: Name of the theorem
            
        Returns:
            Theorem entry or None
        """
        return self.registry['theorems'].get(theorem_name)
    
    def get_skip_set(self) -> Set[str]:
        """Get set of theorem names to skip.
        
        Returns:
            Set of theorem names already in registry
        """
        return set(self.registry['theorems'].keys())
    
    def get_statistics(self) -> Dict:
        """Get statistics about the registry.
        
        Returns:
            Dictionary with statistics
        """
        total = len(self.registry['theorems'])
        naive = sum(1 for t in self.registry['theorems'].values() if t['method'] == 'naive')
        llm = sum(1 for t in self.registry['theorems'].values() if t['method'] == 'llm')
        
        return {
            'total_theorems': total,
            'naive_aesop': naive,
            'llm_assisted': llm,
            'success_rate': f"{total} theorems aesop-ized"
        }
    
    def export_proofs(self, output_file: str):
        """Export all proofs to a Lean file.
        
        Args:
            output_file: Path to output Lean file
        """
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(f"-- Aesop-ized theorems from {self.lean_file_path}\n")
            f.write(f"-- Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
            f.write(f"-- Total theorems: {len(self.registry['theorems'])}\n\n")
            
            for name, entry in sorted(self.registry['theorems'].items()):
                f.write(f"-- {name} ({entry['method']})\n")
                f.write(f"-- Run: {entry['run_id']}\n")
                if entry.get('variant'):
                    f.write(f"-- Variant: {entry['variant']}\n")
                f.write(f"{entry['proof']}\n\n")
    
    def get_registry_path(self) -> Path:
        """Get the path to the registry file.
        
        Returns:
            Path to registry file
        """
        return self.registry_file
    
    def print_summary(self):
        """Print a summary of the registry."""
        stats = self.get_statistics()
        print(f"\n{'='*60}")
        print(f"THEOREM REGISTRY: {self.registry_file.name}")
        print(f"{'='*60}")
        print(f"Lean file: {self.lean_file_path}")
        print(f"Total theorems: {stats['total_theorems']}")
        print(f"  - Naive aesop: {stats['naive_aesop']}")
        print(f"  - LLM-assisted: {stats['llm_assisted']}")
        print(f"Last updated: {self.registry['last_updated']}")
        print(f"{'='*60}")
