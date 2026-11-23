# PROGRESS

One dated entry per session. Each stage followed a written brief (private planning notes, not in this repo).

Repo: GitHub repo `NotItsMe/rim-rule-lean` (branch `master`). Each stage is committed and pushed when it's done.

## 2026-11-22: Stage 10e (the papers' "locally good"; counterexample with nothing cited)

**Done.** Report: `reports/STAGE10e.md`. Stage 10 summary: `reports/STAGE10_SUMMARY.md`.
- **New `RimRule/Mandatory.lean`** (82 lines): `IsMandatory C σ` (Def 2.14: nonempty `σ ∈ Δ(C)` with `¬ ContractibleSpace (realization (link (delta C) σ))`), `LocallyGood C` (Def 2.15: every mandatory face is a codeword), `locallyGood_iff`, and `LocallyGoodC.locallyGood : LocallyGoodC C → LocallyGood C`. Docstring quotes Def 2.13–2.15 of arXiv 1912.00963 v3.
- **New `RimRule/Conj313Literal.lean`** (43 lines): `conj313_counterexample' : ∃ C : Finset (Finset (Fin 7)), IsNeuralCode C ∧ LocallyGood C ∧ ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C` and `Rim70.all70_spec'`. **No cited fact remains.** The old statements are unchanged.
- **Docs:** README and LEAN_FINAL.md say the cited fact is now proved; NOTES.md has the Stage 10 lessons. The old `.lean` docstrings were left unchanged (brief: new files only).
- **Checks:** `lake build` passes (3450 jobs); forbidden-word scan empty; `Check.lean`: all 39 `#print axioms` lines are `[propext, Classical.choice, Quot.sound]`.
- **CI:** GitHub Actions run 45104819300 on commit 4865f7a passed (1 min 42 s).
- **Build:** Mandatory.lean 14 s, Conj313Literal.lean 9–13 s.

**Next:** none planned for Stage 10.

**Blockers:** none.

## 2026-11-22: Stage 10d (collapsible ⇒ contractible)

**Done.** Report: `reports/STAGE10d.md`.
- **New `RimRule/CollapsibleContractible.lean`** (94 lines). `contractibleSpace_realization_of_collapsible : IsComplex K → Collapsible K → ContractibleSpace (realization K)`, by recursion over the collapse list: `nonempty_hequiv_of_collapsesTo` composes the 10c homotopy equivalences; `∅` survives to `{∅, {v}}` (`collapsesTo_subset`), so every free face is nonempty; `isComplex_elemCollapse` keeps each step a complex. Corollary `contractibleSpace_realization_link_of_collapsible` for links in Δ(C).
- **Checks:** `lake build` passes (3446 jobs); forbidden-word scan empty; `Check.lean`: all 35 `#print axioms` lines are `[propext, Classical.choice, Quot.sound]`.
- **CI:** GitHub Actions run 45104413493 on commit 0f1895e passed (1 min 38 s).
- **Build:** CollapsibleContractible.lean 18 s.

**Next:** 10e (literal `LocallyGood`, `conj313_counterexample'`).

**Blockers:** none.

## 2026-11-22: Stage 10c (an elementary collapse is a deformation retraction)

**Done, first attempt.** Report: `reports/STAGE10c.md`.
- **New `RimRule/Collapse.lean`** (292 lines). For a complex `K` and a free pair `(σ, τ)` with `σ ≠ ∅`, `realization_deformationRetract` gives `H : C(unitInterval × |K|, |K|)` with `H(0, x) = x`, `H(1, x) ∈ |K'|` and `H(t, x) = x` on `|K'|` (Hatcher's definition), where `K' = elemCollapse K σ τ`. `realizationCollapseHEquiv` / `nonempty_hequiv_realization_elemCollapse`: `|K| ≃ₕ |K'|`.
- **Map:** `f_t(x) = x + t·m(x)·(|σ| e_w − 𝟙_σ)` with `m(x) = min_{i∈σ} x_i`, `τ = σ ∪ {w}`. One formula on all of `|K|` (m vanishes where the map must be the identity), so no pasting lemma.
- **Checks:** `lake build` passes (3444 jobs); forbidden-word scan empty; `Check.lean`: all 30 `#print axioms` lines are `[propext, Classical.choice, Quot.sound]`.
- **CI:** GitHub Actions run 45104031484 on commit e86e33f passed (2 min 5 s).
- **Build:** Collapse.lean 16–30 s.

**Next:** 10d (collapsible ⇒ contractible).

**Blockers:** none.

## 2026-11-22: Stage 10b (cones: realization is star-convex, hence contractible)

**Done.** Report: `reports/STAGE10b.md`.
- **New `RimRule/Cone.lean`** (75 lines). `starConvex_realization_cone : IsComplex K → IsConeWith K v → StarConvex ℝ (vtx v) (realization K)` and `contractibleSpace_realization_cone : IsComplex K → ∅ ∈ K → IsConeWith K v → ContractibleSpace (realization K)`, via mathlib's `StarConvex.contractibleSpace`. Corollary `contractibleSpace_realization_link_of_hull_ne` (a face that is not its own hull has a contractible link).
- **Checks:** `lake build` passes (3442 jobs); forbidden-word scan empty; `Check.lean` prints `[propext, Classical.choice, Quot.sound]` for all old and new theorems.
- **CI:** GitHub Actions run 45103662434 on commit 5557cc7 passed (1 min 34 s).
- **Build:** Cone.lean 23 s. The release commit's docstring edit to `Defs.lean` forced a full local rebuild; parallel `lake build` ran out of memory (~150 MB free), so modules were built one at a time: 29 min 20 s total.

**Next:** 10c (elementary collapse is a deformation retraction).

**Blockers:** none.

## 2026-11-22: Stage 10a (geometric realization: definition and sanity checks)

**Done.** Brief: the Stage 10 brief (private notes). Only sub-stage 10a; 10b–10e not started.
- **New `RimRule/Realization.lean`** (242 lines). `realization K : Set (Fin n → ℝ)` = points with all `x i ≥ 0`, `∑ i, x i = 1` and support `supp x ∈ K`. Vertex `i` sits at `vtx i = Pi.single i 1`. Docstring quotes Hatcher, *Algebraic Topology* (Δⁿ) and gives the Munkres / Matoušek form `|K| = ⋃_{σ ∈ K} conv {eᵢ : i ∈ σ}`. The quotes were written from memory; check the wording against the books.
- **Sanity theorems:**
  - `realization_singleton_empty : realization {∅} = ∅`, and `not_contractibleSpace_realization_singleton_empty` (so the link `{∅}` of a facet is not contractible: facets are mandatory).
  - `realization_vertex : realization {∅, {v}} = {vtx v}` (one point), and `contractibleSpace_realization_vertex`.
  - `realization_powerset` (the full simplex on σ is the face of Δⁿ⁻¹ vanishing off σ), `realization_powerset_eq_convexHull` (= `conv {eᵢ : i ∈ σ}`), `convex_realization_powerset`, `contractibleSpace_realization_powerset` (σ nonempty; mathlib's `Convex.contractibleSpace`).
  - Extra check against the textbook: `realization_eq_iUnion_convexHull : IsComplex K → realization K = ⋃ σ ∈ K, convexHull ℝ (vtx '' σ)`.
- **No existing file changed** except the import list in `RimRule.lean` and new lines in `Check.lean`.
- **Checks:** forbidden-word scan over `*.lean` returns nothing; `lake build` passes (3440 jobs, only the usual "consider adding `module`" warnings); `lake env lean Check.lean` prints `[propext, Classical.choice, Quot.sound]` for all 13 old and 8 new theorems.
- **CI:** GitHub Actions run 45072901925 on commit 4bbb0b9 passed (`lake build`, 5 min 51 s).
- **Build:** `Realization.lean` builds in 18 s (first check with `lake env lean` took 2 min 15 s, mostly loading mathlib with 0.8 GB RAM free). No memory trouble.

**Next:** 10b (cones are star-convex, hence contractible). mathlib already has `StarConvex.contractibleSpace` in `Mathlib/Analysis/Convex/Contractible.lean`.

**Blockers:** none.

## 2026-11-22: Stage 9 (every missing face; one cited fact; Conjecture 3.13 headline)

**Done.** Brief: DEF_CHECK.md (referee pass on Stage 8). Full write-up: `LEAN_FINAL.md`.
- **New `RimRule/LocallyGood.lean`** (215 lines): `LocallyGoodC C` (every nonempty face of Δ(C) that is not a codeword has a collapsible link), `collapsible_of_cone` (any cone complex collapses to its apex), `collapsible_link_of_hull_ne` (a face that is not its own hull has a cone link), `locallyGoodC_of_certOK`. The 278 certificates are unchanged; the other 1,132 missing faces are covered by the cone lemma, so the old second cited fact (Curto et al. Cor 4.6) is now proved. Only collapsible ⇒ contractible is cited.
- **`all70_spec`** now reads `∀ C ∈ all70, IsNeuralCode C ∧ LocallyGoodC C ∧ ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C`. New `all70_nodup`.
- **New `RimRule/Conj313.lean`**: `conj313_counterexample : ∃ C : Finset (Finset (Fin 7)), IsNeuralCode C ∧ LocallyGoodC C ∧ ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C`.
- **Statement change (stronger):** `Theorem1b` now concludes `¬ IsOpenConvex C ∧ ¬ IsClosedConvex C`, matching the note's 1(b). Old conclusion kept as `theorem1b_open`; closed half from `theorem1a` via `fB_of_h4`. Logged in CHANGES.md.
- **Housekeeping:** Defs.lean cites Chan Def 2.3 for the realized code, explains the `U_∅` convention, notes `∅ ∈ C` is Chan Assumption 2.5. Data.lean header: 1,800 filtered codes, 70 fit. README rewritten. Census.lean comment reworded so the forbidden-word scan is empty.
- **Checks:** forbidden-word scan over `*.lean` returns nothing; `lake build` passes (3424 jobs, only "consider adding `module`" warnings); `lake env lean Check.lean` prints `[propext, Classical.choice, Quot.sound]` for all 13 theorems listed there.
- **CI:** GitHub Actions run 45008594395 on commit 247dc24 passed (`lake build` from scratch, 14 min 34 s).
- **Build:** the parallel `lake build` failed with only ~1.4 GB RAM free (four Lean processes couldn't load mathlib: "failed to read file …Pi.olean"). Built module by module instead: about 22 min total, Links1 335 s, Links2 515 s.

**Blockers:** none.

## 2026-11-22: Stage 8 (70 codes: not convex, and collapsible links)

**Done.** `lake build` passes with no warnings (apart from the usual "consider adding `module`" notes). No existing theorem statement changed; the only edit to an existing file is the import list in `RimRule.lean`.

**Part 1: Theorem 1 on all 70 codes of `data/rim70.json`.**
- `RimRule/Rim70/Data.lean`: the 70 codes and their `openRoles` / `closedRoles`, copied from the JSON. As in `Census.lean`, neurons are `Fin 7` with 0 unused.
- `RimRule/Rim70/Basic.lean`: `Hyps1b C R` (σ_i ≠ ∅, Core, H3, H4) and `Hyps1a C R` (σ_i ≠ ∅, Core, F_B) bundle the hypotheses of `Theorem1b` / `Theorem1a`. There's a `Decidable` instance for `Core`, and `not_convex_of_hyps` applies `theorem1b` and `theorem1a`.
- `RimRule/Rim70/Convex1.lean`, `Convex2.lean`: for each code, `X.hyps : Hyps1b X X.openRoles ∧ Hyps1a X X.closedRoles` by `decide +kernel`, and `X.not_convex : ¬ IsOpenConvex X ∧ ¬ IsClosedConvex X`.

**Part 2: links.**
- `RimRule/Complex.lean` (243 lines) mirrors the papers. It defines `maximal C` (maximal codewords), `delta C` (Δ(C)), `IsComplex`, `link K σ`, free faces, elementary collapses, `CollapsesTo`, `Collapsible` (collapses to a single vertex `{∅, {v}}`), `IsMaxInter` and `LinksCollapsible`.
  - `LinksCollapsible C`: every nonempty σ ∈ Δ(C) that is an intersection of maximal codewords and is not a codeword has a collapsible link `lk_σ(Δ(C))`.
  - Proved general facts: `isComplex_delta`, and `mem_delta_iff_maximal` (Δ(C) is also generated by the maximal codewords, as the paper says).
  - The doc comment states plainly that collapsible ⇒ contractible ⇒ no local obstruction is a cited fact (textbook topology plus Curto et al.), not proved here.
- Certificate checking: `CertOK C cert` = `CertCovers` (every face that needs a certificate has an entry) ∧ `CertValid` (every collapse sequence is valid). `linksCollapsible_of_certOK` turns it into `LinksCollapsible C`.
  - Two helper lemmas keep it fast in the kernel. `link_delta_eq` computes the link straight from C. `hull_eq_of_isMaxInter` says an intersection of maximal codewords equals the intersection of all maximal codewords containing it, so coverage needn't enumerate families of codewords.
- `RimRule/Rim70/Links1.lean`, `Links2.lean`: for each code, `X.cert` (one collapse sequence per face) and `X.linksCollapsible : LinksCollapsible X`, by `decide +kernel` on `CertOK`. There are 278 faces in all.
  - The JSON note says "780 faces". That counts families of maximal codewords: 780 families have a nonempty, non-codeword intersection, and they give 278 distinct faces.

**Summary.** `RimRule/Rim70/Summary.lean`: `all70` (the 70 codes), `length_all70 : all70.length = 70`, and `all70_spec : ∀ C ∈ all70, ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C ∧ LinksCollapsible C`.

**Generated files.** Everything under `RimRule/Rim70/` comes from `scripts/gen_rim70.py`. The script reads `data/rim70.json`, re-checks the hypotheses in Python, finds the collapse sequences (depth-first search), and writes the Lean files. Lean re-checks everything; the script is only a certificate finder.

**Checks.**
- `#print axioms` on `all70_spec` (which depends on all 140 per-code theorems), a sample `not_convex` and `linksCollapsible`, `linksCollapsible_of_certOK`, `hull_eq_of_isMaxInter`, `mem_delta_iff_maximal`, `link_delta_eq`, `theorem1a` and `theorem1b` gives exactly [propext, Classical.choice, Quot.sound].
- No `sorry`, `admit` or `native_decide` (grep finds only the doc comment in Census.lean).

**CI.** GitHub Actions run 44996799795 on commit def015c passed (`lake build` from scratch, 13 min 23 s).

**Build time.** The Stage 8 files take about 15 min locally (Links1 about 11 min, the largest).
- The chunks are chained (Links1 imports Convex1, Links2 imports Convex2), so at most two heavy Lean processes run at once. With four at once, this 8 GB machine crashed Lean (exit code 0xC0000409); each file compiles fine on its own.

**Issues met.**
- The first coverage check enumerated families of maximal codewords with `Finset.powerset` and `Finset.inf`. In the kernel it ran for more than 300 s on one code, and the 2-code prototype hung for about 45 min. Replacing it with the hull test brought it to about 7 s per code.
- The `Decidable` instance for the whole of `CertOK` wasn't found (instance search gave up on the conjunction). Splitting it into `CertCovers` and `CertValid`, each with its own instance, fixed it.

**Line count:** Complex 243; Rim70: Data 847, Basic 44, Convex1/2 264 + 264, Links1/2 474 + 609, Summary 119 (generated); generator 325. Hand-written Lean total: 1070 + 243 = 1313.

**Next:** none planned. Possible extras: drop σ_i ≠ ∅ (referee fix 8), Proposition 2 (apex lift).

**Blockers:** none.

## 2026-11-21: Stage 7 (Theorem 1(a), the closed half, and C5-033 is not closed-convex)

**Done.** `RimRule/Theorem1a.lean` (249 lines) compiles with `lake build`, on the first attempt. The only follow-up was a style warning (`show` that changed the goal, replaced by `change`). The build now has no warnings apart from the usual "consider adding `module`" notes.
- `theorem1a : Theorem1a`. It proves the statement in `Defs.lean` exactly as written; `Defs.lean` is unchanged (`git diff` is empty). Same shape as `theorem1b`: get a, b, z from H5′, H6, H7, then `by_cases` on the overlap.
- `caseA_closed` (overlap, breaks F_A). S = {t ≥ 0 : lineMap a b t ∈ V_j} is closed, so c = inf S lies in S (`IsClosed.csInf_mem`), and c > 0 because a ∉ V_j. H1ₘ puts lineMap a b '' [0, c) in V_k, and c ∈ cl [0, c) (`closure_Ico`), so V_k closed gives the point at c in V_ijkmp.
- `caseB_closed` (no overlap, breaks F_B). Reuses `exists_lowest` from Case B with F = W = V_i ∩ V_j, which is already closed. (a, r) ⊆ V_i ∩ V_m by plain convexity (no Rockafellar 6.1, as the paper says). H1ₘ puts (a, r) in V_k and H2ₘ puts (b, r) in V_l; closedness puts r in both, so c(r) ⊇ ijklm. As in Stage 5, the edge cases (r = a, r = b, h(r) = 0) need no separate case, and the triangle need not be non-degenerate.
- σ_m = ∅ is allowed, as in the paper: nothing in the closed proof uses σ_m ≠ ∅.
- `C033_not_isClosedConvex : ¬ IsClosedConvex Census.C033`. The corollary: Theorem 1(a) applied to `Census.theorem1a_hyps`, roles (4,5,1,2,3,6). With Stage 6, C5-033 is now machine-checked to be neither open-convex nor closed-convex.
- `#print axioms` on `theorem1a`, `C033_not_isClosedConvex`, `caseA_closed` and `caseB_closed` gives exactly [propext, Classical.choice, Quot.sound]. Checked with `lake env lean` on a scratch file (`import RimRule.Theorem1a`).
- No `sorry`, no `admit`, no `native_decide` (grep finds only the doc comment in Census.lean).
- CI: GitHub Actions run 44986033343 on commit dfd043d passed (`lake build`, about 3 min).
- `Theorem1a.lean` builds in about 30 s once its dependencies are built (131 s on the first build, which also rebuilt the import chain). `RimRule.lean` now imports `RimRule.Theorem1a`.

**Line count:** Defs 185, Census 89, Rockafellar 69, CaseA 170, CaseB 256, Main 52, Theorem1a 249. Total 1070.

**Next:** all stages in the brief are done. Possible extras, none started: drop σ_i ≠ ∅ (referee fix 8), the other certificates from the census (brief step 4 says "033 and the other certificates"), or Proposition 2 (apex lift).

**Blockers:** none.

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
