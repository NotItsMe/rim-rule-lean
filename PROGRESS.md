# PROGRESS

One dated entry per session. Brief: BigBrain `Projects/Math Discoveries Files/Lean Rim Brief.md`.

Repo: private GitHub repo `NotItsMe/rim-rule-lean` (branch `master`). Each stage is committed and pushed when it's done.

## 2026-11-21: Stage 6 (Theorem 1(b) assembled, and C5-033 is not open-convex)

**Done.** `RimRule/Main.lean` (52 lines) compiles with `lake build`, on the first attempt.
- `theorem1b : Theorem1b`. It proves the statement in `Defs.lean` exactly as written; `Defs.lean` is unchanged. The proof unpacks `IsOpenConvex`, gets a, b, z from H5′, H6, H7 with `exists_point_of_mem_code` and `mem_inter_iff_subset_codeword`, then splits with `by_cases` on the overlap: Case A (`caseA_realSpace`) or Case B (`caseB_realSpace`).
- `C033_not_isOpenConvex : ¬ IsOpenConvex Census.C033`. The corollary: Theorem 1(b) applied to the census facts `Census.theorem1b_hyps`, roles (4,5,1,2,3,6).
- `#print axioms` on both gives exactly [propext, Classical.choice, Quot.sound]. Checked with `lake env lean` on a scratch file (`import RimRule.Main`), so nothing extra lives in the library.
- No `sorry`, no `admit`, no `native_decide` (grep finds only the doc comment in Census.lean).
- `Main.lean` builds in about 78 s. `RimRule.lean` now imports `RimRule.Main`.

**Line count:** Defs 185, Census 89, Rockafellar 69, CaseA 170, CaseB 256, Main 52. Total 821.

**Next: Stage 7 (optional), Theorem 1(a), the closed half.** Prove `Theorem1a` from `Defs.lean`. A further corollary, "C5-033 is not closed-convex", would then follow from `Census.theorem1a_hyps` the same way.

**Blockers:** none.

## 2026-11-21: Stage 5 (Case B, the lowest-point case of Theorem 1(b))

**Git first.** Stages 0–4 are committed, one commit per stage. Each commit has the `RimRule.lean` imports and PROGRESS entries of its stage. They're pushed to the new private repo `NotItsMe/rim-rule-lean`.

**Done.** `RimRule/CaseB.lean` (256 lines) compiles with `lake build`. It compiled on the first attempt; the only follow-up was fixing two warnings (a deprecated name, and an unused section variable).
- `caseB`: open convex realization (any real topological vector space), σ_i ≠ ∅, H1ₘ, H2ₘ, H3, H4. Take a ∈ U_imp \ U_j, b ∈ U_jmp and z ∈ U_ijm. If [a, b] misses U_i ∩ U_j, that's a contradiction. The Case B hypothesis is written as the exact negation of Case A's, so Stage 6 is a `by_cases`.
- `caseB_realSpace`: the same on ℝ^d.
- **How the lowest point is formalized.** We don't use the height h, so the triangle doesn't have to be non-degenerate. We minimise the z-weight γ over representations (α, β, γ) in the standard 2-simplex with αa + βb + γz ∈ cl W. That set is compact (a closed subset of [0,1]³) and contains (0, 0, 1). This is `exists_lowest`. When the triangle is non-degenerate, γ = h, so r is the paper's point.
- **Key fact.** A representation with z-weight < γ, or = 0, gives a point outside W. The first by minimality, the second because [a, b] misses W. Points of (a, r) and (b, r) have z-weight tγ with t < 1, so they're outside W.
- **Edge cases, all handled by the same argument with no case split:**
  - h(r) = 0 (γ = 0): the "= 0" branch of the key fact.
  - r = a: mathlib's (a, a) = {a}, so it's H1ₘ at a.
  - r = b: H2ₘ at b, with b ∉ U_i from the key fact.
  - B1 of the paper (non-degenerate triangle) isn't needed.
- **Where codewords are read** (referee fix 3): on (a, r) ⊆ U_i (σ_i ≠ ∅); on (b, r) ⊆ U_j (σ_j ≠ ∅ because a ∉ U_j); and at the final point in U_m (σ_m ≠ ∅ from H3 + H4).
- Uses Stage 3: `openSegment_subset_of_isOpen_convex` (6.1) for (a, r) ⊆ U_i and (b, r) ⊆ U_j, and `closure_inter_closure_subset_closure_inter` (6.5) for r ∈ cl (U_k ∩ U_l).
- `#print axioms` on `caseB`, `caseB_realSpace`, `exists_lowest` and `tri_mem_of_convex` gives exactly [propext, Classical.choice, Quot.sound]. No `sorry` and no `native_decide` (grep finds only the doc comment in Census.lean).
- `CaseB.lean` builds in about 30 s, and the full `lake build` takes about 68 s. `RimRule.lean` now imports `RimRule.CaseB`.

**Line count:** Defs 185, Census 89, Rockafellar 69, CaseA 170, CaseB 256. Total 769.

**Next: Stage 6 (main theorem).** Prove `Theorem1b` from `Defs.lean`. Unpack `IsOpenConvex` and get a, b, z from H5′, H6, H7 via `exists_point_of_mem_code`. Then `by_cases` on the overlap and call `caseA_realSpace` or `caseB_realSpace`. Check that `#print axioms Theorem1b`'s proof is clean.

**Blockers:** none.

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
