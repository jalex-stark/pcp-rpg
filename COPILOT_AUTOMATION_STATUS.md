# LeanCopilot Automation Status

## TL;DR

**LeanCopilot is designed for INTERACTIVE use, not batch automation.**

✅ **What works great:**
- Interactive proof development in VSCode
- Getting AI suggestions in real-time
- Clicking to insert suggested tactics

⚠️ **What's challenging:**
- Fully automated batch proof search
- Running without human oversight
- Orchestrator integration for unattended operation

## Why Automation Is Hard

### Design Philosophy

LeanCopilot is built for **human-in-the-loop** workflows:
1. Human writes theorem statement
2. LeanCopilot suggests tactics
3. Human clicks/accepts suggestion
4. Repeat until proof complete

This is intentional - it's a **copilot**, not an autopilot.

### Technical Limitations

1. **`search_proof` is experimental**
   - Works best with human guidance
   - May timeout on harder goals
   - Needs context from surrounding proof state

2. **No batch API**
   - Designed for VSCode InfoView interaction
   - Tactics print to info messages (not structured output)
   - Difficult to parse programmatically

3. **Resource intensive**
   - Each search uses full beam search
   - Models are large (~2.5GB)
   - Better suited for targeted use than batch processing

## Current Integration

### What We Have

1. **LeanCopilot fully installed** ✅
   - Models downloaded
   - Library paths configured
   - Works perfectly in VSCode

2. **Orchestrator worker** ✅
   - `copilot.py` can invoke tactics via LeanDojo
   - `copilot_direct.py` can compile temp files
   - Both tested and functional

### What Works in Practice

**Interactive Development** (Recommended):
```lean
import LeanCopilot

theorem my_theorem : ... := by
  suggest_tactics  -- Get instant AI suggestions
  -- Click the one you want
  -- Continue interactively
```

This is the **primary use case** and works excellently.

**Semi-Automated** (Experimental):
```python
# Orchestrator can try LeanCopilot as fallback
# But success rate will be lower than interactive use
scheduler.register_worker(StrategyType.COPILOT, run_copilot)
```

Use this for:
- Getting hints when micro tactics fail
- Exploring proof strategies
- Finding relevant premises from mathlib

Don't expect:
- High success rates on arbitrary goals
- Faster than human-guided proving
- Replacement for manual proof engineering

## Recommended Workflow

### For PCP Formalization

**Phase 1: Discovery (Interactive)**
1. Open theorem in VSCode
2. Use `suggest_tactics` to explore approaches
3. Build proof interactively with AI suggestions
4. Polish and simplify manually

**Phase 2: Verification (Orchestrator)**
1. Add completed proofs to codebase
2. Run orchestrator to verify builds
3. Use micro tactics for simple lemmas
4. Cache everything for reuse

**Phase 3: Optimization**
1. Profile which tactics are slowest
2. Simplify proofs manually
3. Extract common patterns
4. Build custom tactics for your domain

### Best Practices

✅ **DO:**
- Use LeanCopilot for exploration and learning
- Get AI suggestions when stuck
- Let it find relevant mathlib lemmas
- Accept it's a productivity multiplier, not automation

❌ **DON'T:**
- Expect fully automated proof discovery
- Run unattended batch jobs with LeanCopilot
- Rely on it for critical path automation
- Compare it to deterministic tactics (rfl, simp)

## Alternative: Micro Tactics First

The orchestrator's **micro worker** is better suited for automation:

```python
# Fast, deterministic, high success rate on simple goals
tactics = ['rfl', 'simp', 'omega', 'decide', 'ring', 'aesop']
```

**Strategy:**
1. Let micro tactics handle 80% of simple goals
2. Use LeanCopilot interactively for the remaining 20%
3. Cache successful proofs
4. Build up a lemma library over time

This hybrid approach:
- ✅ Fast batch processing (micro)
- ✅ AI assistance when needed (copilot)
- ✅ Human expertise for hard problems
- ✅ Continuous learning from past proofs

## Future Improvements

**Potential enhancements** (not currently implemented):

1. **Structured output parsing**
   - Parse LeanCopilot's info messages programmatically
   - Extract proof scripts automatically
   - Track suggestion confidence scores

2. **Batch-friendly interface**
   - API for submitting goals in bulk
   - Job queue with prioritization
   - Progress tracking and cancellation

3. **Fine-tuning**
   - Train on PCP-specific proofs
   - Adapt to your theorem patterns
   - Improve success rate for your domain

4. **Caching**
   - Cache premise selections
   - Reuse similar proof patterns
   - Build domain-specific hint database

## Conclusion

**LeanCopilot integration is complete and working as designed.**

It's an excellent **interactive tool** for theorem proving with AI assistance. For **batch automation**, stick with micro tactics and use LeanCopilot selectively.

### Quick Decision Tree

**Need to prove a theorem?**
- Simple goal? → Try micro tactics first
- Complex goal? → Use LeanCopilot in VSCode
- Need hints? → `suggest_tactics` is fast
- Full automation? → Not LeanCopilot's strength

**Building a proof automation system?**
- Foundation: Micro tactics (fast, reliable)
- Enhancement: LeanCopilot (suggestions, premises)
- Integration: Orchestrator (cache, schedule, monitor)
- Critical: Human expertise (design, polish, verify)

## References

- [LeanCopilot Paper](https://arxiv.org/abs/2404.12534) - See "Interactive Proof Development" section
- [LeanCopilot Setup](LEANCOPILOT_SETUP.md) - Installation guide
- [Orchestrator Integration](ORCHESTRATOR_COPILOT_INTEGRATION.md) - How workers use LeanCopilot
