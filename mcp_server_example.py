#!/usr/bin/env python3
"""
MCP Server for Mathlib Aesop Proof Automation

This server exposes theorem proving capabilities via the Model Context Protocol,
allowing any LLM (including Claude Code) to prove Lean theorems interactively.

Usage:
    python mcp_server_example.py

Configuration:
    Set environment variables:
    - KIMINA_SERVER_URL: URL of Kimina validation server (default: http://localhost:8080)
    - LEAN_FILE_PATH: Path to Lean file with theorems (default: data/full_defs_new.lean)
"""

import asyncio
import json
from typing import Any, Dict, List, Optional
from pathlib import Path

# MCP SDK imports (will need: pip install mcp)
from mcp.server import Server, NotificationOptions
from mcp.server.models import InitializationOptions
from mcp.server.stdio import stdio_server
from mcp.types import (
    Tool,
    TextContent,
    ImageContent,
    EmbeddedResource,
    Resource,
    Prompt,
    PromptMessage,
    GetPromptResult,
)

# Import existing functionality
from theorem_extractor import TheoremExtractor
from context.context_builder import ContextBuilder
from context.theorem_analyzer import TheoremAnalyzer
from validators.kimina_validator import KiminaValidator
from theorem_registry import TheoremRegistry

# Initialize server
app = Server("mathlib-aesop-prover")

# Global state (in production, use proper state management)
theorem_extractor = TheoremExtractor()
context_builder = ContextBuilder()
theorem_analyzer = TheoremAnalyzer()
kimina_validator = KiminaValidator()
theorem_registry = TheoremRegistry()

# Configuration
KIMINA_SERVER_URL = "http://localhost:8080"
LEAN_FILE_PATH = Path("data/full_defs_new.lean")


# ============================================================================
# TOOLS
# ============================================================================

@app.list_tools()
async def list_tools() -> list[Tool]:
    """List all available tools."""
    return [
        Tool(
            name="get_theorem",
            description="""Get detailed information about a theorem including its signature,
            dependencies, context, and metadata.

            Parameters:
            - name (string, required): The theorem name (e.g., "eval₂_pow")
            - include_dependencies (boolean, optional): Include dependency list
            - include_context (boolean, optional): Include surrounding context

            Returns theorem details including signature, file location, dependencies,
            imports, patterns detected, and more.""",
            inputSchema={
                "type": "object",
                "properties": {
                    "name": {
                        "type": "string",
                        "description": "The theorem name to look up"
                    },
                    "include_dependencies": {
                        "type": "boolean",
                        "description": "Include theorem dependencies",
                        "default": True
                    },
                    "include_context": {
                        "type": "boolean",
                        "description": "Include surrounding context",
                        "default": True
                    }
                },
                "required": ["name"]
            }
        ),

        Tool(
            name="check_proof",
            description="""Validate a Lean proof using the Kimina proof checker.

            Parameters:
            - theorem (string, required): The theorem name
            - proof (string, required): The Lean proof code to validate
            - timeout_ms (integer, optional): Timeout in milliseconds (default: 5000)

            Returns validation result including whether proof is valid, execution time,
            and any error messages or suggestions.""",
            inputSchema={
                "type": "object",
                "properties": {
                    "theorem": {
                        "type": "string",
                        "description": "The theorem name"
                    },
                    "proof": {
                        "type": "string",
                        "description": "The Lean proof code (e.g., 'by aesop' or full proof term)"
                    },
                    "timeout_ms": {
                        "type": "integer",
                        "description": "Validation timeout in milliseconds",
                        "default": 5000
                    }
                },
                "required": ["theorem", "proof"]
            }
        ),

        Tool(
            name="get_context",
            description="""Get intelligent context for proof generation including imports,
            relevant lemmas, successful strategies from similar theorems, and patterns detected.

            Parameters:
            - theorem (string, required): The theorem name
            - context_type (string, optional): Type of context - "proof_generation", "annotation", or "dependencies"

            Returns rich context including imports, relevant lemmas, detected patterns,
            successful strategies from similar theorems, and more.""",
            inputSchema={
                "type": "object",
                "properties": {
                    "theorem": {
                        "type": "string",
                        "description": "The theorem name"
                    },
                    "context_type": {
                        "type": "string",
                        "enum": ["proof_generation", "annotation", "dependencies"],
                        "description": "Type of context to retrieve",
                        "default": "proof_generation"
                    }
                },
                "required": ["theorem"]
            }
        ),

        Tool(
            name="register_success",
            description="""Register a successful proof in the theorem registry.

            Parameters:
            - theorem (string, required): The theorem name
            - proof (string, required): The successful proof code
            - strategy (string, required): Strategy used (e.g., "NAIVE", "LLM_GUIDED", "CLAUDE_CODE")
            - model (string, optional): Model name that generated the proof
            - attempts (integer, optional): Number of attempts before success
            - lemmas_used (array, optional): List of lemma names used in proof
            - metadata (object, optional): Additional metadata

            Returns registration confirmation with registry ID and suggested annotation.""",
            inputSchema={
                "type": "object",
                "properties": {
                    "theorem": {"type": "string"},
                    "proof": {"type": "string"},
                    "strategy": {"type": "string"},
                    "model": {"type": "string"},
                    "attempts": {"type": "integer", "default": 1},
                    "lemmas_used": {"type": "array", "items": {"type": "string"}},
                    "metadata": {"type": "object"}
                },
                "required": ["theorem", "proof", "strategy"]
            }
        ),

        Tool(
            name="search_theorems",
            description="""Search for theorems by query, namespace, or filter criteria.

            Parameters:
            - query (string, optional): Search query (e.g., "polynomial evaluation")
            - namespace (string, optional): Filter by namespace (e.g., "Mathlib.Algebra.Polynomial")
            - filter (string, optional): Filter type - "all", "proven", "unproven"
            - limit (integer, optional): Maximum results to return

            Returns list of matching theorems with basic metadata.""",
            inputSchema={
                "type": "object",
                "properties": {
                    "query": {"type": "string"},
                    "namespace": {"type": "string"},
                    "filter": {
                        "type": "string",
                        "enum": ["all", "proven", "unproven"],
                        "default": "all"
                    },
                    "limit": {"type": "integer", "default": 20}
                },
                "required": []
            }
        ),

        Tool(
            name="suggest_lemmas",
            description="""Suggest relevant lemmas for proving a theorem based on its signature,
            dependencies, and successful proofs of similar theorems.

            Parameters:
            - theorem (string, required): The theorem name
            - max_results (integer, optional): Maximum number of suggestions

            Returns list of suggested lemmas with confidence scores and reasoning.""",
            inputSchema={
                "type": "object",
                "properties": {
                    "theorem": {"type": "string"},
                    "max_results": {"type": "integer", "default": 5}
                },
                "required": ["theorem"]
            }
        ),

        Tool(
            name="get_failed_attempts",
            description="""Get history of failed proof attempts for a theorem to learn from errors.

            Parameters:
            - theorem (string, required): The theorem name
            - include_errors (boolean, optional): Include full error messages

            Returns list of failed attempts with errors, common issues, and suggestions.""",
            inputSchema={
                "type": "object",
                "properties": {
                    "theorem": {"type": "string"},
                    "include_errors": {"type": "boolean", "default": True}
                },
                "required": ["theorem"]
            }
        ),
    ]


@app.call_tool()
async def call_tool(name: str, arguments: Any) -> list[TextContent]:
    """Handle tool calls from the LLM."""

    if name == "get_theorem":
        return await handle_get_theorem(arguments)
    elif name == "check_proof":
        return await handle_check_proof(arguments)
    elif name == "get_context":
        return await handle_get_context(arguments)
    elif name == "register_success":
        return await handle_register_success(arguments)
    elif name == "search_theorems":
        return await handle_search_theorems(arguments)
    elif name == "suggest_lemmas":
        return await handle_suggest_lemmas(arguments)
    elif name == "get_failed_attempts":
        return await handle_get_failed_attempts(arguments)
    else:
        raise ValueError(f"Unknown tool: {name}")


# ============================================================================
# TOOL HANDLERS
# ============================================================================

async def handle_get_theorem(args: Dict[str, Any]) -> list[TextContent]:
    """Get detailed theorem information."""
    theorem_name = args["name"]
    include_deps = args.get("include_dependencies", True)
    include_context = args.get("include_context", True)

    # Extract theorem from Lean file
    theorems = theorem_extractor.extract_from_file(LEAN_FILE_PATH)
    theorem = next((t for t in theorems if t["name"] == theorem_name), None)

    if not theorem:
        return [TextContent(
            type="text",
            text=json.dumps({"error": f"Theorem '{theorem_name}' not found"})
        )]

    # Build response
    result = {
        "name": theorem["name"],
        "signature": theorem["signature"],
        "file_location": str(LEAN_FILE_PATH),
        "line_number": theorem.get("line_number"),
    }

    if include_deps:
        # Analyze dependencies
        analysis = theorem_analyzer.analyze(theorem)
        result["dependencies"] = analysis.get("dependencies", [])
        result["patterns_detected"] = analysis.get("patterns", [])

    if include_context:
        # Build context
        context = context_builder.build_context(theorem)
        result["imports"] = context.get("imports", [])
        result["section_context"] = context.get("section", "unknown")
        result["surrounding_lemmas"] = context.get("lemmas", [])

    return [TextContent(type="text", text=json.dumps(result, indent=2))]


async def handle_check_proof(args: Dict[str, Any]) -> list[TextContent]:
    """Validate a proof using Kimina."""
    theorem_name = args["theorem"]
    proof_code = args["proof"]
    timeout_ms = args.get("timeout_ms", 5000)

    # Get theorem
    theorems = theorem_extractor.extract_from_file(LEAN_FILE_PATH)
    theorem = next((t for t in theorems if t["name"] == theorem_name), None)

    if not theorem:
        return [TextContent(
            type="text",
            text=json.dumps({"error": f"Theorem '{theorem_name}' not found"})
        )]

    # Construct full theorem with proof
    full_code = f"{theorem['signature']} := {proof_code}"

    # Validate with Kimina
    try:
        validation_result = await kimina_validator.validate(
            code=full_code,
            timeout_ms=timeout_ms
        )

        result = {
            "valid": validation_result.get("valid", False),
            "execution_time_ms": validation_result.get("execution_time_ms"),
            "error": validation_result.get("error"),
            "suggestions": validation_result.get("suggestions", [])
        }

        return [TextContent(type="text", text=json.dumps(result, indent=2))]

    except Exception as e:
        return [TextContent(
            type="text",
            text=json.dumps({"valid": False, "error": str(e)})
        )]


async def handle_get_context(args: Dict[str, Any]) -> list[TextContent]:
    """Get context for proof generation."""
    theorem_name = args["theorem"]
    context_type = args.get("context_type", "proof_generation")

    # Get theorem
    theorems = theorem_extractor.extract_from_file(LEAN_FILE_PATH)
    theorem = next((t for t in theorems if t["name"] == theorem_name), None)

    if not theorem:
        return [TextContent(
            type="text",
            text=json.dumps({"error": f"Theorem '{theorem_name}' not found"})
        )]

    # Build context
    context = context_builder.build_context(theorem, context_type=context_type)

    # Add successful strategies from registry
    similar_proofs = theorem_registry.get_similar_proofs(theorem_name)
    context["successful_strategies"] = [
        p.get("strategy") for p in similar_proofs
    ]

    # Add relevant lemmas based on analysis
    analysis = theorem_analyzer.analyze(theorem)
    context["relevant_lemmas"] = analysis.get("suggested_lemmas", [])
    context["patterns_detected"] = analysis.get("patterns", [])

    return [TextContent(type="text", text=json.dumps(context, indent=2))]


async def handle_register_success(args: Dict[str, Any]) -> list[TextContent]:
    """Register a successful proof."""
    theorem_name = args["theorem"]
    proof = args["proof"]
    strategy = args["strategy"]
    model = args.get("model", "unknown")
    attempts = args.get("attempts", 1)
    lemmas_used = args.get("lemmas_used", [])
    metadata = args.get("metadata", {})

    # Register in theorem registry
    registry_id = theorem_registry.register_success(
        theorem_name=theorem_name,
        proof=proof,
        strategy=strategy,
        model=model,
        attempts=attempts,
        lemmas_used=lemmas_used,
        metadata=metadata
    )

    # Generate suggested annotation
    suggested_annotation = generate_aesop_annotation(proof, lemmas_used)

    result = {
        "registered": True,
        "registry_id": registry_id,
        "suggested_annotation": suggested_annotation,
        "timestamp": metadata.get("timestamp")
    }

    return [TextContent(type="text", text=json.dumps(result, indent=2))]


async def handle_search_theorems(args: Dict[str, Any]) -> list[TextContent]:
    """Search for theorems."""
    query = args.get("query")
    namespace = args.get("namespace")
    filter_type = args.get("filter", "all")
    limit = args.get("limit", 20)

    # Extract all theorems
    theorems = theorem_extractor.extract_from_file(LEAN_FILE_PATH)

    # Filter by namespace
    if namespace:
        theorems = [t for t in theorems if namespace in t.get("namespace", "")]

    # Filter by proven/unproven
    if filter_type == "proven":
        proven_names = theorem_registry.get_proven_theorem_names()
        theorems = [t for t in theorems if t["name"] in proven_names]
    elif filter_type == "unproven":
        proven_names = theorem_registry.get_proven_theorem_names()
        theorems = [t for t in theorems if t["name"] not in proven_names]

    # Search by query (simple substring match)
    if query:
        query_lower = query.lower()
        theorems = [
            t for t in theorems
            if query_lower in t["name"].lower() or
               query_lower in t.get("signature", "").lower()
        ]

    # Limit results
    theorems = theorems[:limit]

    result = {
        "count": len(theorems),
        "theorems": [
            {
                "name": t["name"],
                "signature": t["signature"][:100] + "..." if len(t["signature"]) > 100 else t["signature"],
                "line_number": t.get("line_number")
            }
            for t in theorems
        ]
    }

    return [TextContent(type="text", text=json.dumps(result, indent=2))]


async def handle_suggest_lemmas(args: Dict[str, Any]) -> list[TextContent]:
    """Suggest relevant lemmas for a theorem."""
    theorem_name = args["theorem"]
    max_results = args.get("max_results", 5)

    # Get theorem
    theorems = theorem_extractor.extract_from_file(LEAN_FILE_PATH)
    theorem = next((t for t in theorems if t["name"] == theorem_name), None)

    if not theorem:
        return [TextContent(
            type="text",
            text=json.dumps({"error": f"Theorem '{theorem_name}' not found"})
        )]

    # Analyze and suggest lemmas
    analysis = theorem_analyzer.analyze(theorem)
    suggested = analysis.get("suggested_lemmas", [])[:max_results]

    result = {
        "theorem": theorem_name,
        "suggested_lemmas": suggested,
        "reasoning": analysis.get("reasoning", "Based on theorem signature and patterns"),
        "confidence_scores": [0.9 - (i * 0.1) for i in range(len(suggested))]  # Mock scores
    }

    return [TextContent(type="text", text=json.dumps(result, indent=2))]


async def handle_get_failed_attempts(args: Dict[str, Any]) -> list[TextContent]:
    """Get failed proof attempts."""
    theorem_name = args["theorem"]
    include_errors = args.get("include_errors", True)

    # Get failed attempts from registry
    failed_attempts = theorem_registry.get_failed_attempts(theorem_name)

    # Analyze common issues
    common_issues = analyze_common_errors(failed_attempts)

    result = {
        "theorem": theorem_name,
        "attempt_count": len(failed_attempts),
        "attempts": failed_attempts if include_errors else [],
        "common_issues": common_issues,
        "suggestions": generate_suggestions_from_errors(common_issues)
    }

    return [TextContent(type="text", text=json.dumps(result, indent=2))]


# ============================================================================
# RESOURCES
# ============================================================================

@app.list_resources()
async def list_resources() -> list[Resource]:
    """List available resources."""
    return [
        Resource(
            uri="mathlib://theorems/all",
            name="All Theorems",
            mimeType="application/json",
            description="List of all theorems in the loaded Lean file"
        ),
        Resource(
            uri="mathlib://proof-registry",
            name="Proof Registry",
            mimeType="application/json",
            description="Registry of all successfully proven theorems"
        ),
        Resource(
            uri="mathlib://statistics",
            name="Proof Statistics",
            mimeType="application/json",
            description="Statistics about proof success rates and strategies"
        )
    ]


@app.read_resource()
async def read_resource(uri: str) -> str:
    """Read a resource by URI."""
    if uri == "mathlib://theorems/all":
        theorems = theorem_extractor.extract_from_file(LEAN_FILE_PATH)
        return json.dumps(theorems, indent=2)

    elif uri == "mathlib://proof-registry":
        registry = theorem_registry.get_all_proofs()
        return json.dumps(registry, indent=2)

    elif uri == "mathlib://statistics":
        stats = theorem_registry.get_statistics()
        return json.dumps(stats, indent=2)

    else:
        raise ValueError(f"Unknown resource: {uri}")


# ============================================================================
# PROMPTS
# ============================================================================

@app.list_prompts()
async def list_prompts() -> list[Prompt]:
    """List available prompts."""
    return [
        Prompt(
            name="aesop_proof_generation",
            description="Generate an aesop-based proof for a theorem",
            arguments=[
                {"name": "theorem", "description": "Theorem name", "required": True},
                {"name": "context", "description": "Additional context", "required": False}
            ]
        ),
        Prompt(
            name="error_recovery",
            description="Recover from a proof validation error",
            arguments=[
                {"name": "theorem", "description": "Theorem name", "required": True},
                {"name": "error", "description": "Error message", "required": True},
                {"name": "previous_proof", "description": "Previous proof attempt", "required": True}
            ]
        )
    ]


@app.get_prompt()
async def get_prompt(name: str, arguments: Dict[str, str]) -> GetPromptResult:
    """Get a prompt by name."""
    if name == "aesop_proof_generation":
        theorem_name = arguments["theorem"]
        additional_context = arguments.get("context", "")

        # Load system prompt template
        with open("aesop_agent/prompts/system_prompt.txt") as f:
            template = f.read()

        # Get context
        theorems = theorem_extractor.extract_from_file(LEAN_FILE_PATH)
        theorem = next((t for t in theorems if t["name"] == theorem_name), None)

        context = context_builder.build_context(theorem) if theorem else {}

        # Format prompt
        prompt_text = template.format(
            theorem=theorem["signature"] if theorem else "",
            imports="\n".join(context.get("imports", [])),
            lemmas="\n".join(context.get("lemmas", [])),
            additional=additional_context
        )

        return GetPromptResult(
            messages=[
                PromptMessage(
                    role="user",
                    content=TextContent(type="text", text=prompt_text)
                )
            ]
        )

    elif name == "error_recovery":
        # Load retry prompt template
        with open("aesop_agent/prompts/retry_prompt.txt") as f:
            template = f.read()

        prompt_text = template.format(
            theorem=arguments["theorem"],
            error=arguments["error"],
            previous_proof=arguments["previous_proof"]
        )

        return GetPromptResult(
            messages=[
                PromptMessage(
                    role="user",
                    content=TextContent(type="text", text=prompt_text)
                )
            ]
        )

    else:
        raise ValueError(f"Unknown prompt: {name}")


# ============================================================================
# HELPER FUNCTIONS
# ============================================================================

def generate_aesop_annotation(proof: str, lemmas_used: List[str]) -> str:
    """Generate @[aesop] annotation suggestion from proof."""
    if "by aesop" in proof and "add safe apply" in proof:
        return "@[aesop safe apply]"
    elif "by aesop" in proof and "add norm simp" in proof:
        return "@[aesop norm simp]"
    elif "induction" in proof.lower():
        return "@[aesop safe apply (by induction)]"
    else:
        return "@[aesop safe apply]"


def analyze_common_errors(failed_attempts: List[Dict]) -> List[str]:
    """Analyze common error patterns."""
    errors = [attempt.get("error", "") for attempt in failed_attempts]

    common = []
    if any("syntax" in e.lower() for e in errors):
        common.append("syntax errors in aesop configuration")
    if any("no progress" in e.lower() for e in errors):
        common.append("aesop cannot make progress on goal")
    if any("timeout" in e.lower() for e in errors):
        common.append("proof validation timeout")

    return common


def generate_suggestions_from_errors(common_issues: List[str]) -> List[str]:
    """Generate suggestions based on common errors."""
    suggestions = []

    for issue in common_issues:
        if "syntax" in issue:
            suggestions.append("Check aesop syntax - use 'add safe apply' or 'add norm simp'")
        elif "no progress" in issue:
            suggestions.append("Try adding relevant lemmas with 'add safe apply lemma_name'")
        elif "timeout" in issue:
            suggestions.append("Simplify proof or increase timeout")

    return suggestions


# ============================================================================
# MAIN
# ============================================================================

async def main():
    """Run the MCP server."""
    async with stdio_server() as (read_stream, write_stream):
        await app.run(
            read_stream,
            write_stream,
            InitializationOptions(
                server_name="mathlib-aesop-prover",
                server_version="0.1.0",
                capabilities=app.get_capabilities(
                    notification_options=NotificationOptions(),
                    experimental_capabilities={}
                )
            )
        )


if __name__ == "__main__":
    asyncio.run(main())
