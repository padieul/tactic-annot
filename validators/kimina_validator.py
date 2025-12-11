"""Kimina validator - wraps Kimina client for proof validation."""

from typing import Tuple
from kimina_client import KiminaClient


class KiminaValidator:
    """Validates Lean proofs using the Kimina server."""
    
    def __init__(self, client: KiminaClient):
        """Initialize with a Kimina client.
        
        Args:
            client: KiminaClient instance
        """
        self.client = client
    
    def validate_proof(self, full_code: str, timeout: int = 60) -> Tuple[bool, str, float]:
        """Validate a Lean proof.
        
        Args:
            full_code: Complete Lean code including imports
            timeout: Validation timeout in seconds
            
        Returns:
            Tuple of (is_valid, error_message, time_taken)
        """
        try:
            response = self.client.check(full_code, timeout=timeout)
            result = response.results[0]
            analysis = result.analyze()
            
            if analysis.status == "valid":
                return True, "", result.time
            else:
                # Collect error messages
                error_msgs = []
                if result.response and result.response.get("messages"):
                    for msg in result.response["messages"]:
                        if msg["severity"] == "error":
                            error_msgs.append(msg['data'])
                error_text = "\n".join(error_msgs) if error_msgs else f"Validation failed: {analysis.status}"
                return False, error_text, result.time
                
        except Exception as e:
            return False, f"Validation exception: {str(e)}", 0.0
    
    def apply_code_fixes(self, code: str) -> str:
        """Apply standard code fixes for known issues.
        
        Args:
            code: Lean code to fix
            
        Returns:
            Fixed code
        """
        # Fix induction_on' syntax: 'add' -> 'h_add', 'monomial' -> 'h_monomial'
        code = code.replace('| add ', '| h_add ')
        code = code.replace('| monomial ', '| h_monomial ')
        
        # Fix namespace issue: map_dvd needs _root_ prefix in eval₂RingHom context
        code = code.replace(
            'map_dvd (eval₂RingHom',
            '_root_.map_dvd (eval₂RingHom'
        )
        
        return code
