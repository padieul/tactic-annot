# Claude Code + MCP Server Demo

## How It Would Work

### 1. Install and Configure MCP Server

```bash
# Install the MCP server
pip install mathlib-aesop-prover

# Configure Claude Code to use it
# Edit ~/.claude/mcp_servers.json (or .claude/mcp_servers.json in project)
```

**`.claude/mcp_servers.json`**:
```json
{
  "mathlib-aesop-prover": {
    "command": "python",
    "args": ["-m", "mcp_server"],
    "cwd": "/home/user/tactic-annot",
    "env": {
      "KIMINA_SERVER_URL": "http://localhost:8080"
    }
  }
}
```

---

## Example Session 1: Single Theorem Proving

### User Prompt:
```
Prove the theorem eval₂_pow using aesop tactics
```

### Claude Code Workflow:

**Step 1**: Get theorem details
```
Using tool: mcp__mathlib-aesop-prover__get_theorem
Parameters: {
  "name": "eval₂_pow",
  "include_dependencies": true,
  "include_context": true
}

Result:
{
  "signature": "theorem eval₂_pow (n : Nat) : (p ^ n).eval₂ f x = p.eval₂ f x ^ n",
  "file": "Mathlib.Algebra.Polynomial.Eval.Defs",
  "dependencies": ["eval₂_one", "eval₂_mul", "pow_succ", "pow_zero"],
  "section_context": "semiring",
  "patterns_detected": ["nat_induction_candidate"]
}
```

**Step 2**: Get proof context
```
Using tool: mcp__mathlib-aesop-prover__get_context
Parameters: {
  "theorem": "eval₂_pow",
  "context_type": "proof_generation"
}

Result:
{
  "imports": ["Mathlib.Algebra.Ring.Defs", "Mathlib.Data.Nat.Basic"],
  "relevant_lemmas": ["eval₂_one", "eval₂_mul", "pow_succ"],
  "successful_strategies": [
    "induction on Nat with aesop in branches",
    "simp with eval₂_one, eval₂_mul"
  ],
  "similar_theorems": ["eval_pow", "eval₂_mul"]
}
```

**Step 3**: Generate proof (Claude's reasoning)
```
Based on the context:
- This is a Nat induction case (pattern detected)
- Dependencies include eval₂_one (base case) and eval₂_mul (inductive step)
- Similar theorems use induction + simp strategy

I'll try an induction-based proof:
```

**Step 4**: Validate proof
```
Using tool: mcp__mathlib-aesop-prover__check_proof
Parameters: {
  "theorem": "eval₂_pow",
  "proof": "by induction n with | zero => simp [pow_zero, eval₂_one] | succ n ih => simp [pow_succ, eval₂_mul, ih]"
}

Result:
{
  "valid": true,
  "execution_time_ms": 189,
  "error": null
}
```

**Step 5**: Register success
```
Using tool: mcp__mathlib-aesop-prover__register_success
Parameters: {
  "theorem": "eval₂_pow",
  "proof": "by induction n with | zero => simp [pow_zero, eval₂_one] | succ n ih => simp [pow_succ, eval₂_mul, ih]",
  "strategy": "CLAUDE_CODE_INDUCTION",
  "model": "claude-opus-4.5",
  "attempts": 1,
  "lemmas_used": ["eval₂_one", "eval₂_mul", "pow_succ", "pow_zero"]
}

Result:
{
  "registered": true,
  "registry_id": "eval₂_pow_20260104_143022",
  "suggested_annotation": "@[aesop safe apply (by induction)]"
}
```

### Claude's Response to User:
```
✓ Successfully proved eval₂_pow!

Proof:
theorem eval₂_pow (n : Nat) : (p ^ n).eval₂ f x = p.eval₂ f x ^ n := by
  induction n with
  | zero => simp [pow_zero, eval₂_one]
  | succ n ih => simp [pow_succ, eval₂_mul, ih]

Strategy: Natural induction on n
- Base case (n=0): Uses pow_zero and eval₂_one
- Inductive step: Uses pow_succ, eval₂_mul, and induction hypothesis

Suggested annotation: @[aesop safe apply (by induction)]

Registered in proof registry: eval₂_pow_20260104_143022
```

---

## Example Session 2: Batch Proving with Error Recovery

### User Prompt:
```
Prove all theorems in Mathlib.Algebra.Polynomial.Eval.Defs that aren't
already proven. Show me progress as you go.
```

### Claude Code Workflow:

**Step 1**: Search unproven theorems
```
Using tool: mcp__mathlib-aesop-prover__search_theorems
Parameters: {
  "namespace": "Mathlib.Algebra.Polynomial.Eval.Defs",
  "filter": "unproven",
  "limit": 50
}

Result: Found 19 unproven theorems
```

**Step 2**: Iterate through theorems
```
Progress: 1/19 - eval₂_eq_zero_of_dvd_of_eval₂_eq_zero

Using tool: mcp__mathlib-aesop-prover__get_context
→ Found relevant lemmas: eval₂_dvd, Dvd.dvd

Attempt 1:
Using tool: mcp__mathlib-aesop-prover__check_proof
Proof: "by aesop"
Result: { "valid": false, "error": "no progress on goal" }

Attempt 2 (with hints):
Using tool: mcp__mathlib-aesop-prover__check_proof
Proof: "by aesop (add safe apply eval₂_dvd)"
Result: { "valid": false, "error": "partial progress, stuck on Dvd.dvd" }

Attempt 3 (with more hints):
Using tool: mcp__mathlib-aesop-prover__check_proof
Proof: "by aesop (add norm simp [eval₂_dvd, Dvd.dvd])"
Result: { "valid": true }

✓ Registered success

Progress: 2/19 - eval₂_comp
... [continues]
```

### Claude's Progressive Output:
```
Starting batch proof generation for 19 theorems...

✓ eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (attempt 3/5) - 234ms
✓ eval₂_comp (attempt 1/5) - 156ms
✗ eval₂_hom_complex (attempt 5/5) - Failed
  Error: Missing commutativity lemma for complex ring
✓ eval₂_map (attempt 2/5) - 289ms
...

Summary:
- Proven: 16/19 (84.2%)
- Failed: 3/19
  - eval₂_hom_complex: missing lemmas
  - eval₂_ring_hom: syntax error (needs manual fix)
  - eval₂_algebraMap: fundamental limitation

All successful proofs registered in proof registry.
```

---

## Example Session 3: Annotation Generation

### User Prompt:
```
Generate @[aesop] annotations for all successfully proven theorems
in the registry and create a PR-ready file
```

### Claude Code Workflow:

**Step 1**: Get registry
```
Using tool: mcp__mathlib-aesop-prover__get_resource
Resource: mathlib://proof-registry

Result: 105 successful proofs loaded
```

**Step 2**: Generate annotations
```
Using tool: mcp__mathlib-aesop-prover__generate_annotation
For each theorem:
  - Analyze proof strategy
  - Determine aesop rule type (safe/unsafe apply/forward)
  - Generate annotation syntax
  - Validate annotation doesn't break existing proofs
```

**Step 3**: Create annotated file
```
Created: annotations_proposal.lean

theorem eval₂_pow (n : Nat) : (p ^ n).eval₂ f x = p.eval₂ f x ^ n := by
  induction n with
  | zero => simp [pow_zero, eval₂_one]
  | succ n ih => simp [pow_succ, eval₂_mul, ih]

@[aesop safe apply]
theorem eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (h : p ∣ q) (h0 : eval₂ f x p = 0) :
    eval₂ f x q = 0 := by
  aesop (add norm simp [eval₂_dvd, Dvd.dvd])

... [105 more theorems]
```

**Step 4**: Validate annotations
```
Using tool: mcp__mathlib-aesop-prover__check_proof
Validating that annotations work correctly...

✓ All 105 annotations validated successfully
```

### Claude's Response:
```
✓ Generated @[aesop] annotations for 105 theorems

Created file: annotations_proposal.lean

Breakdown by annotation type:
- @[aesop safe apply]: 73 theorems
- @[aesop safe forward]: 18 theorems
- @[aesop norm simp]: 14 theorems

All annotations validated against Lean compiler.
Ready to submit as PR to Mathlib!

Next steps:
1. Review annotations in annotations_proposal.lean
2. Run full Mathlib CI to ensure no regressions
3. Create PR with: git commit -m "feat: add aesop annotations to Polynomial.Eval.Defs"
```

---

## Example Session 4: Interactive Debugging

### User Prompt:
```
The theorem eval₂_hom_complex is failing. Help me understand why
and suggest a fix.
```

### Claude Code Workflow:

**Step 1**: Get failure history
```
Using tool: mcp__mathlib-aesop-prover__get_failed_attempts
Parameters: { "theorem": "eval₂_hom_complex" }

Result:
{
  "attempts": [
    {
      "model": "qwen-480b",
      "proof": "by aesop",
      "error": "no progress on goal",
      "timestamp": "2025-12-12T03:15:22Z"
    },
    {
      "model": "claude-opus-4.5",
      "proof": "by aesop (add safe apply RingHom.map_mul)",
      "error": "unsolved goals: ⊢ Complex.ofReal commutes with _",
      "timestamp": "2026-01-04T14:22:11Z"
    }
  ],
  "common_issues": ["missing commutativity lemma"],
  "similar_failures": ["eval₂_hom_real", "eval₂_algebraMap"]
}
```

**Step 2**: Get theorem details
```
Using tool: mcp__mathlib-aesop-prover__get_theorem
Parameters: { "name": "eval₂_hom_complex" }

Result:
{
  "signature": "theorem eval₂_hom_complex (f : ℝ →+* ℂ) : ...",
  "goal": "Show that eval₂ commutes with complex ring homomorphism",
  "required_lemmas": ["Complex.ofReal_mul", "Complex.ofReal_add"]
}
```

**Step 3**: Search for missing lemmas
```
Using tool: mcp__mathlib-aesop-prover__search_theorems
Parameters: { "query": "Complex.ofReal commutative" }

Result:
Found:
- Complex.ofReal_mul (a b : ℝ) : ofReal (a * b) = ofReal a * ofReal b
- Complex.ofReal_add (a b : ℝ) : ofReal (a + b) = ofReal a + ofReal b
```

**Step 4**: Suggest fix
```
Using tool: mcp__mathlib-aesop-prover__suggest_lemmas
Parameters: { "theorem": "eval₂_hom_complex" }

Result:
{
  "recommended_lemmas": [
    "Complex.ofReal_mul",
    "Complex.ofReal_add",
    "RingHom.map_mul",
    "RingHom.map_add"
  ],
  "suggested_proof": "by aesop (add norm simp [Complex.ofReal_mul, Complex.ofReal_add, RingHom.map_mul])"
}
```

**Step 5**: Test suggested fix
```
Using tool: mcp__mathlib-aesop-prover__check_proof
Parameters: {
  "theorem": "eval₂_hom_complex",
  "proof": "by aesop (add norm simp [Complex.ofReal_mul, Complex.ofReal_add, RingHom.map_mul])"
}

Result: { "valid": true, "execution_time_ms": 412 }
```

### Claude's Response:
```
Found the issue! The proof was failing because aesop didn't know about
Complex.ofReal commutativity lemmas.

Previous attempts:
- qwen-480b: Basic aesop → no progress
- claude-opus-4.5: Added RingHom.map_mul → partial progress but stuck

Root cause: Missing Complex.ofReal_mul and Complex.ofReal_add lemmas

✓ Fixed proof:
theorem eval₂_hom_complex (f : ℝ →+* ℂ) : ... := by
  aesop (add norm simp [Complex.ofReal_mul, Complex.ofReal_add, RingHom.map_mul])

Validated successfully in 412ms.

Registered in proof registry with metadata:
- Required lemmas: Complex.ofReal_mul, Complex.ofReal_add
- Failure pattern: Missing commutativity
- Similar cases: eval₂_hom_real, eval₂_algebraMap (can use same strategy)
```

---

## Why This is Better Than Current Approach

### **For Users**
1. **Natural Language**: Just ask Claude to prove theorems
2. **Interactive**: Can debug, iterate, and refine in conversation
3. **Transparent**: See exactly which tools are being used
4. **Learnable**: Understand proof strategies through dialogue

### **For Developers**
1. **LLM Agnostic**: Same MCP server works with GPT, Qwen, local models
2. **Composable**: Can combine with other MCP servers (filesystem, git, etc.)
3. **Reusable**: Other projects can use your MCP server
4. **Maintainable**: Clean separation between proof logic and LLM interface

### **For Researchers**
1. **Comparable**: Easy to benchmark different LLMs
2. **Extensible**: Add new tools without changing LLM code
3. **Shareable**: Publish MCP server, others can reproduce results
4. **Standardized**: MCP protocol is well-documented and supported

---

## Performance Expectations

Based on your current results (84.7% with Qwen-480B), with Claude Code:

**Expected Success Rate: 88-92%**
- Claude Opus 4.5 has stronger reasoning than Qwen-480B (non-reasoning)
- Better tool use capabilities
- Can leverage all your context building and lemma suggestion

**Workflow Improvements:**
- Interactive debugging → faster iteration
- Natural language → better prompt engineering
- Progress tracking → user visibility
- Error recovery → learn from mistakes in session

---

## Next Steps to Build This

1. **Start with MCP server skeleton** (1 day)
2. **Wrap 3 core tools** (1 day):
   - get_theorem
   - check_proof
   - get_context
3. **Test manually with Claude Code** (1 day)
4. **Iterate and expand** (ongoing)

Want me to help you start building the MCP server implementation?
