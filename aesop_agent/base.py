"""Abstract base class for autoformalization models."""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Any


@dataclass
class AesopisationRequest:
    """Request for autoformalization."""

    lean_theorem_str: str  # The theorem text (with or without proof)
    context: Optional[str] = None  # Additional Lean context (imports, definitions)
    max_tokens: int = 512
    temperature: float = 0.0
    n_versions: int = 1  # Number of parallel proof versions to generate
    max_retries: int = 1  # Max retries per version with error feedback
    previous_attempts: Optional[List[Dict[str, str]]] = None  # List of {attempt, error} for retry context
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class AesopisationResult:
    """Result of an autoformalization attempt."""

    formal_statement: str
    success: bool
    error_message: Optional[str] = None
    metadata: Dict[str, Any] = field(default_factory=dict)


class AesopAgentBase(ABC):
    """Abstract base class for external autoformalization models.

    These are pre-trained models used as tools in the data generation pipeline,
    not models we're training/researching.
    """

    def __init__(self, model_name: str):
        self.model_name = model_name
        self._initialized = False

    @abstractmethod
    def initialize(self) -> None:
        """Load model weights and prepare for inference."""
        pass

    @abstractmethod
    def autoformalize(
        self, request: AesopisationRequest
    ) -> AesopisationResult:
        """Convert natural language to formal Lean 4 statement.

        Args:
            request: AesopisationRequest with natural language input

        Returns:
            AesopisationResult with formal statement or error
        """
        pass

    @abstractmethod
    def batch_autoformalize(
        self, requests: List[AesopisationRequest]
    ) -> List[AesopisationResult]:
        """Batch autoformalization for efficiency.

        Args:
            requests: List of AesopisationRequest objects

        Returns:
            List of AesopisationResult objects
        """
        pass

    def shutdown(self) -> None:
        """Clean up resources. Override if needed."""
        self._initialized = False

    @property
    def is_initialized(self) -> bool:
        """Check if model is initialized."""
        return self._initialized

    def __enter__(self):
        """Context manager entry."""
        self.initialize()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.shutdown()
