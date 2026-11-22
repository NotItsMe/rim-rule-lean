# PROGRESS

One dated entry per session. Brief: BigBrain `Projects/Math Discoveries Files/Lean Rim Brief.md`.

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
