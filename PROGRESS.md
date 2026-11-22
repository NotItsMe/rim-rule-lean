# PROGRESS

One dated entry per session. Brief: BigBrain `Projects/Math Discoveries Files/Lean Rim Brief.md`.

## 2026-11-21: Stage 4 (Case A, the overlap case of Theorem 1(b))

**Done.** `RimRule/CaseA.lean` (170 lines) compiles with `lake build`. It compiled on the second attempt; the only error was a `▸` cast, fixed with `rw`.
- `caseA`: in an open convex realization (any real topological vector space), with σ_i ≠ ∅, H1ₘ and F_A, take a ∈ U_imp \ U_j and b ∈ U_jmp. If some point of [a, b] lies in U_i ∩ U_j, that's a contradiction (`False`).
- `caseA_realSpace`: the same statement on ℝ^d = `Fin d → ℝ`, the space used in `IsOpenConvex`.
- The proof follows the council note §2 Case A with the referee's repair: H1ₘ is applied at c itself, and c ∉ U_j covers both c = a and c > a.
- How "the first point of the U_j part" is found: parametrize [a, b] by `lineMap a b t`. Let S = {t > 0 : lineMap a b t ∈ U_j} and c = inf S. S is open, so c ∉ S. c is in the closure of S, so the open preimage of U_ikmp around c meets S. That replaces the ball in the paper with an open interval in the parameter.
- Helpers, reusable in Stage 5 and 6: `mem_inter_union` (U_{σ∪τ} = U_σ ∩ U_τ), `mem_X_of_mem_inter` (σ ≠ ∅ ⇒ U_σ ⊆ X, referee fix 3), `codeword_mem_of_mem_X`, `isOpen_inter`, `convex_inter`.
- b ∈ U_j isn't used in Case A. Only b ∈ U_mp is. I kept the paper's hypothesis b ∈ U_jmp anyway so the Stage 6 call is direct.
- `#print axioms` on `caseA`, `caseA_realSpace` and `mem_inter_union` gives exactly [propext, Classical.choice, Quot.sound]. No `sorry` and no `native_decide` (grep finds only the doc comment in Census.lean).
- `CaseA.lean` imports only `RimRule.Defs`. It builds in about 22 s, and the full `lake build` takes about 57 s.
- `RimRule.lean` now imports `RimRule.CaseA`.

**Line count:** Defs 185, Census 89, Rockafellar 69, CaseA 170. Total 513.

**Next: Stage 5 (Case B, the lowest-point case).** Same setting, plus z ∈ U_ijm and the assumption that [a, b] misses W = U_i ∩ U_j. Show T = conv(a, b, z) is non-degenerate, take r lowest in cl W ∩ T, and get [a, r) ⊆ U_k and [b, r) ⊆ U_l. Then r ∈ cl U_k ∩ cl U_l = cl (U_k ∩ U_l) (Stage 3 + H3), and r ∈ U_m breaks H4. Handle r = a, r = b and h(r) = 0 explicitly. NOTES.md has the barycentric-weight idea that may avoid building h.

**Blockers:** none.

## 2026-11-21: Stage 3 (Rockafellar 6.5, trial run)

**Done.** `RimRule/Rockafellar.lean` (69 lines) compiles with `lake build`. It compiled on the first attempt, so the trial run passes and we can go on to Stage 4.
- `closure_inter_closure_subset_closure_inter`: the ⊇ direction the Rim proof uses. If U, V are open, convex and U ∩ V is nonempty, then cl U ∩ cl V ⊆ cl (U ∩ V).
- `closure_inter_eq_of_isOpen_convex`: the full equality cl (U ∩ V) = cl U ∩ cl V. The ⊆ direction is mathlib's `closure_inter_subset_inter_closure`.
- Both hold in any real topological vector space. `rockafellar_6_5` states the brief's version on ℝ^d = `Fin d → ℝ`.
- Helper `openSegment_subset_of_isOpen_convex` is Rockafellar 6.1 for open convex U: (w, x) ⊆ U when w ∈ U and x ∈ cl U. Stage 5 will reuse it for [a, r) ⊆ U_k.
- Proof: pick w ∈ U ∩ V. Rockafellar 6.1 puts (w, x) inside both U and V, and x lies in the closure of (w, x) by `segment_subset_closure_openSegment`.
- `#print axioms` on all three theorems gives exactly [propext, Classical.choice, Quot.sound]. No `sorry` and no `native_decide`. `grep` finds only a doc comment in Census.lean that says "no `native_decide`".
- The file imports only `Mathlib.Analysis.Convex.Topology`, the same import as Defs.lean. It builds in about 23 s, and the full `lake build` takes about 58 s.
- `RimRule.lean` now imports `RimRule.Rockafellar`.

**Line count:** Defs 185, Census 89, Rockafellar 69. Total 343.

**Next: Stage 4 (Case A, the overlap case of Theorem 1(b)).** Points a ∈ U_imp \ U_j and b ∈ U_jmp. If U_i and U_j overlap on [a, b], let c be the first point of the U_j part. H1ₘ applies at c, and a ball around c inside U_ikmp meets U_j, which breaks F_A. To find "the first point", take the infimum of {t : lineMap a b t ∈ U_j} on [0, 1].

**Blockers:** none.

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
