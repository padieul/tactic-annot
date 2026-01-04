# MCP Server Architecture Pivot - Quick Start Guide

## 🎯 Vision

Transform tactic-annot from a standalone LLM-calling system into a **reusable MCP server** that any LLM can use to prove Lean theorems interactively.

### Before (Current Architecture)
```
┌─────────────────────────────────────┐
│   main.py                           │
│   ├─> calls Nebius API directly    │
│   ├─> custom prompting logic       │
│   └─> hardcoded retry strategies   │
└─────────────────────────────────────┘
         Only works with Qwen via Nebius
```

### After (MCP Architecture)
```
┌─────────────────────────────────────┐
│   MCP Server (mathlib-aesop-prover) │
│   ├─> Exposes tools via MCP        │
│   ├─> Resources for theorems       │
│   └─> Prompts for proof generation │
└─────────────────────────────────────┘
         ▲         ▲           ▲
         │         │           │
    Claude Code   GPT-4    Any LLM
```

---

## 🚀 Why This is Better

### **Technical Advantages**
1. **LLM Agnostic**: Works with Claude, GPT, Qwen, local models, future models
2. **Tool-Based**: Modern LLMs excel at tool use (better than custom prompting)
3. **Reusable**: Entire Lean/Mathlib community can use your server
4. **Composable**: Combine with other MCP servers (git, filesystem, web)
5. **Future-Proof**: As LLMs improve, same server gets better results

### **Research Advantages**
1. **Comparable**: Easy to benchmark different LLMs on same tasks
2. **Reproducible**: Others can run your exact setup
3. **Extensible**: Add new tools without changing LLM code
4. **Publishable**: MCP servers are shareable and discoverable

### **User Experience Advantages**
1. **Natural Language**: Just talk to Claude Code - it uses tools automatically
2. **Interactive**: Debug, iterate, refine in conversation
3. **Transparent**: See exactly which tools are being called
4. **Progressive**: See results in real-time, not just batch output

---

## 📋 Implementation Roadmap

### **Phase 1: MVP (2-3 days)**
- [ ] Setup MCP server framework
- [ ] Wrap 3 core tools: `get_theorem`, `check_proof`, `get_context`
- [ ] Test manually with Claude Code
- [ ] Validate can prove at least 10 theorems

**Deliverable**: Working MCP server that Claude Code can use

### **Phase 2: Feature Parity (2-3 days)**
- [ ] Add all tools from current system
- [ ] Implement resources (theorem list, registry)
- [ ] Add MCP prompts (aesop generation, error recovery)
- [ ] Match current 84.7% success rate

**Deliverable**: MCP server with full current functionality

### **Phase 3: Demo & Documentation (1-2 days)**
- [ ] Create Claude Code demo workflows
- [ ] Write comprehensive docs
- [ ] Record demo video
- [ ] Prepare for community release

**Deliverable**: Polished demo ready to share

### **Phase 4: Advanced Features (2-3 days)**
- [ ] Enhanced lemma suggestion
- [ ] Grind tactic support
- [ ] Annotation generation pipeline
- [ ] Multi-model comparison tools

**Deliverable**: Production-ready system

### **Phase 5: Community Release (1-2 days)**
- [ ] Publish to MCP server registry
- [ ] PyPI package
- [ ] Blog post / paper draft
- [ ] Lean Zulip announcement

**Deliverable**: Public release

---

## 🛠️ Getting Started (Today!)

### **Step 1: Install MCP SDK**
```bash
cd /home/user/tactic-annot
pip install mcp
```

### **Step 2: Create Basic Server**
```bash
mkdir -p mcp_server/tools
touch mcp_server/__init__.py
touch mcp_server/server.py
```

Use `mcp_server_example.py` as starting point (already created for you!)

### **Step 3: Test Manually**
```bash
# Run MCP server
python mcp_server_example.py

# In another terminal, test with MCP inspector
npx @modelcontextprotocol/inspector python mcp_server_example.py
```

### **Step 4: Configure Claude Code**
```bash
# Create Claude Code config
mkdir -p .claude
cat > .claude/mcp_servers.json << 'EOF'
{
  "mathlib-aesop-prover": {
    "command": "python",
    "args": ["-m", "mcp_server_example"],
    "cwd": "/home/user/tactic-annot"
  }
}
EOF
```

### **Step 5: Test with Claude Code**
Open Claude Code and try:
```
Prove the theorem eval₂_pow using the mathlib-aesop-prover MCP server
```

Claude Code will automatically:
1. Call `get_theorem` to understand the theorem
2. Call `get_context` to get relevant lemmas
3. Generate a proof
4. Call `check_proof` to validate
5. Call `register_success` if it works

---

## 📊 Expected Results

### **Performance Comparison**

| Metric | Current (Qwen-480B) | Expected (Claude Code) |
|--------|---------------------|------------------------|
| Success Rate | 84.7% (105/124) | **88-92%** (109-114/124) |
| Avg Time/Theorem | ~3s | ~4s (more tool calls) |
| Interactive? | No (batch only) | **Yes** (real-time) |
| Multi-LLM? | No (Qwen only) | **Yes** (any LLM) |
| Error Recovery | Automatic | **Interactive + Automatic** |
| User Control | Low (config only) | **High** (conversational) |

### **Why Claude Code Should Beat Qwen-480B**
1. **Better Reasoning**: Claude Opus 4.5 > Qwen-480B (non-reasoning)
2. **Tool Use**: Claude optimized for tool calling
3. **Interactive Debugging**: Can refine in conversation
4. **Context Integration**: Better use of provided context

### **Plus You Get**
- Same server works with GPT-4o (test immediately)
- Same server works with future models (zero refactoring)
- Community can contribute improvements
- Others can build on your work

---

## 📚 Files Created for You

1. **`mcp_implementation_plan.md`** - Detailed implementation plan with phases, tasks, architecture diagrams
2. **`claude_code_example.md`** - Concrete examples of Claude Code workflows (single theorem, batch, annotation generation, debugging)
3. **`mcp_server_example.py`** - Working MCP server code with all tools implemented
4. **`MCP_PIVOT_README.md`** (this file) - Quick start guide

---

## 🎓 Learning Resources

### **MCP Protocol**
- Official docs: https://modelcontextprotocol.io/
- Python SDK: https://github.com/modelcontextprotocol/python-sdk
- Example servers: https://github.com/modelcontextprotocol/servers

### **Claude Code MCP Integration**
- Use the Task tool with `subagent_type='claude-code-guide'` to ask questions about Claude Code MCP setup
- Example: "How do I configure an MCP server in Claude Code?"

### **Testing MCP Servers**
- MCP Inspector: `npx @modelcontextprotocol/inspector`
- Manual testing: Use stdio input/output
- Integration testing: Create test LLM client

---

## 💡 Key Design Decisions

### **1. Tools vs Resources vs Prompts**

**Tools** (for actions):
- `check_proof` - validate a proof
- `register_success` - save successful proof
- `suggest_lemmas` - get lemma recommendations

**Resources** (for data):
- `mathlib://theorems/all` - list all theorems
- `mathlib://proof-registry` - view successful proofs
- `mathlib://statistics` - see metrics

**Prompts** (for templates):
- `aesop_proof_generation` - system prompt for proof gen
- `error_recovery` - retry prompt with error feedback

### **2. Sync vs Async**
Use async throughout for:
- Non-blocking Kimina validation
- Concurrent theorem processing
- Better performance with multiple requests

### **3. State Management**
Options:
- **Simple**: Global variables (MVP)
- **Better**: Class-based state
- **Production**: Database (SQLite/PostgreSQL)

Start simple, evolve as needed.

### **4. Error Handling**
MCP tools should:
- Return structured errors (JSON with error field)
- Never throw exceptions to LLM
- Provide actionable error messages
- Suggest next steps when possible

---

## 🔬 Experiment Ideas

Once MCP server is working, you can easily test:

### **Model Comparison**
```python
# Test same theorems with different models
models = [
    "claude-opus-4.5",
    "gpt-4o",
    "qwen-480b",
    "deepseek-v3"
]

for model in models:
    results = run_proof_generation(theorems, model, mcp_server)
    compare_success_rates(results)
```

### **Strategy Testing**
```python
# Test different proof strategies
strategies = [
    "naive_aesop_only",
    "with_lemma_hints",
    "with_induction_detection",
    "interactive_refinement"
]
```

### **Ablation Studies**
- With/without context building
- With/without error feedback
- With/without lemma suggestions
- Different temperature strategies

---

## 🎯 Success Criteria

### **Week 1 MVP**
- [ ] MCP server runs and exposes 3+ tools
- [ ] Claude Code can connect and use tools
- [ ] Can prove at least 10 theorems interactively
- [ ] Basic error handling works

### **Week 2 Feature Parity**
- [ ] All current functionality exposed via MCP
- [ ] Success rate matches or exceeds 84.7%
- [ ] Works with Claude Code + at least 1 other LLM
- [ ] Comprehensive documentation

### **Week 3 Community Ready**
- [ ] Published to MCP registry
- [ ] Demo video created
- [ ] At least 3 example workflows documented
- [ ] Positive feedback from 1+ external tester

---

## 🚦 Next Steps (Immediate)

### **Right Now**
1. Review the created files (`mcp_server_example.py`, `claude_code_example.md`)
2. Decide if this pivot makes sense for your goals
3. Install MCP SDK: `pip install mcp`

### **Today**
4. Run the example MCP server
5. Test with MCP inspector
6. Try manually calling tools

### **This Week**
7. Get basic Claude Code integration working
8. Prove first theorem via MCP server
9. Iterate on tool design based on usage

### **Next Week**
10. Add remaining tools
11. Test with multiple LLMs
12. Prepare demo for community

---

## ❓ FAQ

**Q: Will this replace the current system entirely?**
A: You can keep `main.py` as a legacy option. MCP server uses same underlying code (TheoremExtractor, KiminaValidator, etc.) - it's just a different interface.

**Q: How much work is this?**
A: ~7-10 days for production-ready system. MVP in 2-3 days.

**Q: Can I still use Qwen models?**
A: Yes! Create a generic LLM client that connects to MCP server and calls Nebius API. Same flexibility, better architecture.

**Q: What if MCP protocol changes?**
A: MCP is by Anthropic, actively maintained, and designed for stability. Breaking changes are rare and well-communicated.

**Q: Is this worth it for a research project?**
A: **Absolutely**. Benefits:
- More impactful (reusable by community)
- Better for paper (tool-based approach is novel)
- Future-proof (works with new models automatically)
- More citations (others build on your work)

**Q: Can I test this with Claude Code right now?**
A: Yes! The `mcp_server_example.py` is functional. Just install MCP SDK and configure `.claude/mcp_servers.json`.

---

## 🎉 Why This is Exciting

This pivot transforms your project from:
- **A research experiment** → **Community infrastructure**
- **Model-specific tool** → **Universal proof assistant**
- **Batch processor** → **Interactive system**
- **One-off implementation** → **Extensible platform**

And you get to **demo Claude Code proving Lean theorems in natural language** - which is genuinely impressive and publishable!

---

## 📞 Need Help?

- **MCP Protocol Questions**: Check official docs at modelcontextprotocol.io
- **Claude Code Questions**: Use Task tool with `subagent_type='claude-code-guide'`
- **Implementation Questions**: I'm here to help! Just ask.

---

**Ready to build the future of automated theorem proving? Let's start! 🚀**
