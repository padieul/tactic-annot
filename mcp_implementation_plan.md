# MCP Server Implementation Plan

## Phase 1: Core MCP Server (2-3 days)

### 1.1 Setup MCP Server Framework
- [ ] Install MCP SDK: `pip install mcp`
- [ ] Create `mcp_server/` directory structure
- [ ] Setup stdio transport for local testing
- [ ] Implement server initialization and shutdown

### 1.2 Wrap Existing Functionality as MCP Tools
- [ ] `get_theorem` - wrap TheoremExtractor
- [ ] `check_proof` - wrap KiminaValidator
- [ ] `get_context` - wrap ContextBuilder
- [ ] `validate_aesop` - basic syntax validation
- [ ] `register_success` - wrap TheoremRegistry

### 1.3 Implement Resources
- [ ] `mathlib://theorems/{namespace}` - list theorems by namespace
- [ ] `mathlib://proof-registry` - access to successful proofs
- [ ] `mathlib://theorem/{name}` - single theorem details

### 1.4 Add MCP Prompts
- [ ] `aesop_proof_generation` - port from prompts/system_prompt.txt
- [ ] `error_recovery` - port from prompts/retry_prompt.txt

---

## Phase 2: Generic LLM Client (1-2 days)

### 2.1 Create MCP Client
- [ ] Python client that connects to MCP server
- [ ] Supports any OpenAI-compatible API endpoint
- [ ] Configuration for different models (Claude, GPT, Qwen)

### 2.2 Proof Generation Loop
- [ ] Iterative proof generation using MCP tools
- [ ] Error feedback loop
- [ ] Temperature decay strategy
- [ ] Success/failure logging

### 2.3 Multi-Model Testing
- [ ] Test with Claude Opus/Sonnet
- [ ] Test with GPT-4o
- [ ] Test with Qwen (via Nebius)
- [ ] Compare performance across models

---

## Phase 3: Claude Code Integration Demo (1 day)

### 3.1 MCP Server Configuration
- [ ] Create `.claude/mcp_servers.json` config
- [ ] Document how to install and configure
- [ ] Add example queries and workflows

### 3.2 Demo Workflows
- [ ] Single theorem proving with Claude Code
- [ ] Batch proving with progress tracking
- [ ] Error recovery and refinement
- [ ] Annotation generation from successful proofs

### 3.3 Documentation
- [ ] README with Claude Code setup instructions
- [ ] Video/gif demo of Claude Code proving theorems
- [ ] Example conversations and commands

---

## Phase 4: Advanced Features (2-3 days)

### 4.1 Enhanced Context Tools
- [ ] `get_dependencies` - dependency graph extraction
- [ ] `search_theorems` - semantic search
- [ ] `suggest_lemmas` - ML-based lemma suggestion
- [ ] `get_failed_attempts` - historical error analysis

### 4.2 Annotation Generation
- [ ] Tool: `generate_annotation` - suggest @[aesop] annotations
- [ ] Tool: `validate_annotation` - check annotation correctness
- [ ] Batch annotation pipeline

### 4.3 Grind Tactic Support
- [ ] Add support for grind tactic proofs
- [ ] Grind-specific prompts and strategies
- [ ] Compare aesop vs grind effectiveness

---

## Phase 5: Community Release (1-2 days)

### 5.1 Packaging
- [ ] PyPI package for MCP server
- [ ] Docker image for easy deployment
- [ ] NPM package (if TypeScript rewrite)

### 5.2 Documentation
- [ ] Full API documentation
- [ ] Tutorial: Using with Claude Code
- [ ] Tutorial: Using with other LLMs
- [ ] Contributing guidelines

### 5.3 Publication
- [ ] Publish to MCP server registry
- [ ] Blog post / paper draft
- [ ] Demo video
- [ ] GitHub release with examples

---

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────┐
│  MCP Server (mathlib-aesop-prover)                      │
│  ┌───────────────────────────────────────────────────┐  │
│  │ MCP Protocol Layer                                │  │
│  │  - stdio transport                                │  │
│  │  - Tool registration                              │  │
│  │  - Resource management                            │  │
│  │  - Prompt templates                               │  │
│  └───────────────────────────────────────────────────┘  │
│  ┌───────────────────────────────────────────────────┐  │
│  │ Business Logic (existing codebase)                │  │
│  │  - TheoremExtractor                               │  │
│  │  - ContextBuilder                                 │  │
│  │  - KiminaValidator                                │  │
│  │  - TheoremRegistry                                │  │
│  │  - TheoremAnalyzer                                │  │
│  └───────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────┘
                         ▲
                         │ MCP Protocol
                         │
        ┌────────────────┼────────────────┐
        │                │                │
   ┌────▼─────┐    ┌────▼──────┐   ┌────▼─────┐
   │  Claude  │    │  Generic  │   │  Custom  │
   │   Code   │    │    LLM    │   │  Client  │
   │  (demo)  │    │  Client   │   │  (yours) │
   └──────────┘    └───────────┘   └──────────┘
```

---

## File Structure

```
tactic-annot/
├── mcp_server/
│   ├── __init__.py
│   ├── server.py                    # Main MCP server
│   ├── tools/
│   │   ├── __init__.py
│   │   ├── theorem_tools.py         # get_theorem, search_theorems
│   │   ├── proof_tools.py           # check_proof, validate_aesop
│   │   ├── context_tools.py         # get_context, suggest_lemmas
│   │   └── registry_tools.py        # register_success, get_failed_attempts
│   ├── resources/
│   │   ├── __init__.py
│   │   ├── theorem_resources.py     # mathlib://theorems/*
│   │   └── registry_resources.py    # mathlib://proof-registry
│   ├── prompts/
│   │   ├── __init__.py
│   │   └── aesop_prompts.py         # MCP prompt templates
│   └── config.py
│
├── clients/
│   ├── generic_llm_client/
│   │   ├── __init__.py
│   │   ├── mcp_client.py            # MCP client wrapper
│   │   ├── proof_loop.py            # Iterative proving logic
│   │   └── model_configs.py         # Claude, GPT, Qwen configs
│   │
│   └── claude_code_demo/
│       ├── .claude/
│       │   └── mcp_servers.json     # Claude Code MCP config
│       ├── demo_workflow.md         # Example usage
│       └── example_session.txt      # Sample conversation
│
├── existing codebase...
│   ├── main.py (legacy - can deprecate)
│   ├── theorem_extractor.py
│   ├── context/
│   ├── validators/
│   └── ...
│
├── docs/
│   ├── mcp_server_api.md
│   ├── claude_code_setup.md
│   ├── generic_llm_setup.md
│   └── architecture.md
│
└── tests/
    ├── test_mcp_tools.py
    ├── test_mcp_resources.py
    └── test_integration.py
```

---

## Success Metrics

### MCP Server Quality
- [ ] All existing functionality available via MCP tools
- [ ] Response time < 2s for most tools
- [ ] Comprehensive error handling
- [ ] 100% of current features exposed

### Claude Code Integration
- [ ] Can prove theorems interactively
- [ ] Natural language → proof workflow works
- [ ] Error recovery demonstrates learning
- [ ] Matches or exceeds current 84.7% success rate

### Community Impact
- [ ] Published to MCP server registry
- [ ] 5+ GitHub stars in first week
- [ ] At least 1 external user/contributor
- [ ] Positive feedback from Lean community

---

## Risk Mitigation

### Risk: MCP Server Performance
- **Mitigation**: Cache theorem metadata, use async tools
- **Fallback**: Optimize hot paths, add batching

### Risk: Claude Code Integration Complexity
- **Mitigation**: Start with simple examples, iterate
- **Fallback**: Provide detailed docs and example sessions

### Risk: Adoption by Community
- **Mitigation**: Clear docs, demos, easy setup
- **Fallback**: Direct outreach to Lean community, Zulip posts

---

## Timeline

**Total: ~7-10 days of focused work**

- Week 1: Core MCP server + generic LLM client
- Week 2: Claude Code demo + advanced features
- Week 3: Polish, docs, community release

## Next Steps

1. **Immediate**: Create MCP server skeleton
2. **Day 1**: Implement core tools (get_theorem, check_proof)
3. **Day 2**: Test with Claude Code manually
4. **Day 3**: Build generic LLM client
5. **Day 4+**: Iterate based on testing
