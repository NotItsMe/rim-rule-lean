# PROGRESS

One dated entry per session. Brief: BigBrain `Projects/Math Discoveries Files/Lean Rim Brief.md`.

## 2026-11-21: Stage 2 (Census)

**Done.** `RimRule/Census.lean` (89 lines) compiles with `lake build`. It has no `sorry` and no `native_decide`.
- C5-033 is entered from `data/C5-033.md` (13 codewords; labels 1..6 in `Fin 7`, neuron 0 unused). Roles are (i,j,k,l,m,p) = (4,5,1,2,3,6).
- This matches the council note's letter form of 033 codeword for codeword (ikmp = 1346, jlmp = 2356, ijkm = 1345, and so on).
- Proved by `decide +kernel`: H1ₘ, H2ₘ, H3, H4, H5′, H6, H7, F_A and F_B, each as its own theorem.
- Bundled as `theorem1b_hyps` (σ_i ≠ ∅, Core, H3, H4) and `theorem1a_hyps` (σ_i ≠ ∅, Core, F_B). So both theorem statements are non-vacuous.
- Data checks:
  - `card_C033`: 13 codewords.
  - `facets033_correct`: the maximal codewords are exactly 12, 1345, 1346, 2345, 2356.
  - `isNeuralCode_C033`: ∅ is a codeword.
- Negative controls:
  - `control_no_apex`: with m = ∅, H4 fails.
  - `control_drop_1346`: without 1346, H5′ fails.
- `#print axioms` on all of the above gives exactly [propext, Classical.choice, Quot.sound]. That rules out `Lean.ofReduceBool`.
- `Census.lean` builds in about 26 s.

**Changes to `Defs.lean`:** I added a `Decidable` instance for `IsNeuralCode` (185 lines now). No statement changed, so CHANGES.md is unchanged.

**Issues met:**
- Plain `decide` hit max recursion depth on the 13-codeword code. `decide +kernel` works, as the brief allows. See NOTES.md.
- My first negative control (swap k and m) was wrong: k ∪ l ∪ m is still {1,2,3}. The kernel rejected it, and I replaced it with the m = ∅ control.

**General X:** kept. Stage 2 doesn't touch realizations, so nothing to switch.

**Next: Stage 3 (Rockafellar 6.5, the trial run).** For open convex U, V with U ∩ V ≠ ∅, prove closure U ∩ closure V ⊆ closure (U ∩ V). NOTES.md has the plan via `Convex.openSegment_interior_closure_subset_interior`.

**Blockers:** none.

## 2026-11-21: Stages 0 and 1

**Stage 0 (Setup): done.**
- Lean 4.36.0 and mathlib v4.36.0 were already installed. Didn't reinstall.
- `lake build` passed on the template project (about 16 s).

**Stage 1 (Defs): done.**
- `RimRule/Defs.lean` (182 lines) compiles with `lake build`. It has no `sorry` and no `native_decide`.
- Removed the template `RimRule/Basic.lean`. `RimRule.lean` now imports `RimRule.Defs`.
- What it defines, each next to the paper's wording (council part-2 note, §5):
  - `IsNeuralCode`, `codeword` (c(x)), `inter` (U_σ), `codeOf`, `IsRealization` (U_s ⊆ X, C = {c(x) : x ∈ X}).
  - `IsOpenConvex` and `IsClosedConvex`, over ℝ^d = `Fin d → ℝ` with an arbitrary stimulus space X.
  - `Roles` (σ_i … σ_p), the hypotheses `H1m H2m H3 H4 H5' H6 H7 FA FB`, and `Core`.
  - `Decidable` instances for every hypothesis, so `decide` can check them.
  - The basic fact `mem_inter_iff_subset_codeword` (x ∈ U_σ ⇔ σ ⊆ c(x)). It's proved, and its axioms are [propext, Classical.choice, Quot.sound].
  - The targets as `Prop`s: `Theorem1b` (open, Rim\*) and `Theorem1a` (closed).
- Sanity check, done in a scratch file outside the library: `decide` proves Core + F_B for C10 with roles (k,l,i,j,p) = (1,2,3,4,5), m = ∅. It also proves ¬H4 there, as it should. Checking took about 24 s.
- Build cost: a clean build of `Defs.lean` takes about 50 s. It imports only `Mathlib.Analysis.Convex.Topology`.

**Warnings (harmless):** Lake suggests adding `module` because mathlib uses the module system. I left it out on purpose: plain `import` works, and `module` would require `public` annotations.

**Next: Stage 2 (Census).** Write `Census.lean`: H1ₘ … F_A, H3 and H4 hold on C5-033 with roles (4,5,1,2,3,6), checked by `decide`. First get 033's exact codewords and neuron numbering from `NotItsMe/neural-codes-96` data/codes.json. The council note's letter form is {ikmp, jlmp, ijkm, ijlm, kl, mp, ikm, jlm, ijm, k, l, m, ∅}.

**Blockers:** none.
