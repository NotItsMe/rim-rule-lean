# NOTES: math and formalization decisions

## Conventions (Stage 1)
- **Neurons** are `Fin n`, so labels are 0-based. For readability in the census, use `Fin (n+1)` and leave 0 unused, so the paper's labels 1..n stay as they are.
- **Codes** are `Finset (Finset (Fin n))`, which makes every hypothesis decidable. A realization's code is a `Set`, and `IsRealization` says the two are equal via the coercion.
- **ℝ^d** is `Fin d → ℝ`, not `EuclideanSpace ℝ (Fin d)`. The topology and convexity are the same, and the import is much lighter. The definitions (`codeword`, `inter`, `codeOf`, `IsRealization`) are generic over any type `E`, so later proofs can work in any real topological vector space and then specialise.
- **Stimulus space X** is arbitrary (Chan Def 2.4), with U_s ⊆ X. This is the paper's general version and is stronger than the X = ℝ^d simplification the brief allows. Cost: when we read c(x) we must know x ∈ X. Every such point lies in some U_s with s in a nonempty role (σ_i, σ_j, or σ_m in open Case B), as in referee fix 3.
- **∅ ∈ C** is *not* assumed in `Theorem1a/1b`. That makes them stronger statements. `IsNeuralCode` is still defined, to mirror the paper.
- **σ_i ≠ ∅** is kept as a hypothesis, as in the paper. Referee fix 8 says it could be dropped, but that's optional.
- "Contains t" means `R.t ⊆ c`. Unions of roles are `Finset` unions, e.g. H5′ is `R.i ∪ R.m ∪ R.p ⊆ c ∧ ¬ R.j ⊆ c`.
- ~~`Theorem1b` doesn't add "therefore not closed-convex".~~ Changed 2026-11-22 (Stage 9): `Theorem1b` now concludes `¬ IsOpenConvex C ∧ ¬ IsClosedConvex C`, as in the note's 1(b). The open half is `theorem1b_open`; the closed half is `theorem1a` via `fB_of_h4` (H4 ⇒ F_B).

## mathlib names confirmed in the installed version (v4.36.0)
- `Convex.openSegment_interior_closure_subset_interior`: `Mathlib/Analysis/Convex/Topology.lean:142`. This is Rockafellar 6.1 for interiors. Our U are open, so interior U = U.
- `Convex.combo_interior_closure_subset_interior` (same file, line 87)
- `Convex.closure` (same file, line 216)
- `Convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior`: `Mathlib/Analysis/Convex/Intrinsic.lean:452`

## Rockafellar (Stage 3), done
- `segment_subset_closure_openSegment` (`Mathlib/Analysis/Convex/Topology.lean:58`) gives `[x -[ℝ] y] ⊆ closure (openSegment ℝ x y)`. Use it with `right_mem_segment ℝ w x` to show x ∈ cl (w, x).
- `closure_inter_subset_inter_closure` is the easy ⊆ direction of 6.5.
- Our wrapper `RimRule.openSegment_subset_of_isOpen_convex` (6.1 with `interior U = U`) is the form Case B needs.

## Case A (Stage 4), done
- Work in the parameter t ∈ ℝ with `f := AffineMap.lineMap a b` (type `ℝ →ᵃ[ℝ] E`), not with balls in E. Facts used:
  - `AffineMap.lineMap_continuous`, `AffineMap.lineMap_apply_zero`, `AffineMap.lineMap_apply_one`.
  - `segment_eq_image_lineMap` turns "x ∈ [a, b]" into "x = f t, t ∈ Icc 0 1".
  - `Convex.affine_preimage` then `Convex.ordConnected` (alias of `convex_iff_ordConnected`): preimages of convex sets are intervals, so `.out` gives `Icc x y ⊆ s`.
  - `csInf_mem_closure`, `csInf_le`, `le_csInf`, and the root `mem_closure_iff` (open set around a closure point meets the set).
  - mathlib has no ready lemma "the inf of an open set in ℝ is not in it". Proved inline with `mem_nhds_iff_exists_Ioo_subset`: if c ∈ S, (l + c)/2 ∈ S is below c.
- `S = Ioi 0 ∩ f⁻¹' U_j` (not `Icc 0 1 ∩ …`) keeps S open; t₀ > 0 follows from a ∉ U_j.
- U_σ open/convex: `isOpen_biInter_finset`, `convex_iInter₂`.
- `h ▸ x` failed for goals of the form `0 ∈ f ⁻¹' s` (the cast can't see `f 0` through the preimage). Use `rw [mem_preimage, hf0]` instead.

## Case B (Stage 5), done
- **Decision:** the lowest point minimises the z-weight over *representations* in the 2-simplex (`simplex3 ⊆ ℝ × ℝ × ℝ`, map `tri a b z q = q.1•a + q.2.1•b + q.2.2•z`), not the affine height h over points. This removes the non-degeneracy step (paper B1) and merges the r = a, r = b and h(r) = 0 cases into one argument.
- Compactness: `isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)` then `IsCompact.of_isClosed_subset`, then `IsCompact.inter_right` with a closed preimage, then `IsCompact.exists_isMinOn` + `isMinOn_iff`.
- `Set.setOf_and` is deprecated in this mathlib; use `Set.ofPred_and`.
- Convexity of a 3-point combination: `Convex.sum_mem` over `Fin 3` with `![…]`, then `fin_cases i <;> simpa` and `Fin.sum_univ_three`.
- Re-weighting `s•a + t•(tri w)` as `tri (s + t w₁, t w₂, t w₃)`: `simp only [tri, smul_add, smul_smul, add_smul]; abel`. The simplex sum is `linear_combination hst + t * hwsum`.
- `mul_lt_of_lt_one_left : 0 < b → a < 1 → a * b < b` gives tγ < γ.
- mathlib's `openSegment ℝ a a = {a}` (not empty). That is why r = a needs no special case.
- `exists_point_of_mem_code`: c ∈ C ⇒ some x ∈ X has codeword c. Stage 6 will use it to get a, b, z from H5′, H6, H7.

## Main theorem (Stage 6), done
- `Theorem1b` is a `def … : Prop`, so `theorem theorem1b : Theorem1b` starts with `intro` (it unfolds by definition).
- The points: `obtain ⟨a, -, rfl⟩ := exists_point_of_mem_code hR hca` replaces the codeword by `codeword U a`, then `mem_inter_iff_subset_codeword` gives a ∈ U_σ directly. x ∈ X isn't needed here; Cases A and B recover it from σ_i ≠ ∅ / σ_j ≠ ∅ / σ_m ≠ ∅.
- The Case B hypothesis is literally `¬` of the Case A one, so `by_cases` needs no rewriting.

## Theorem 1(a), closed (Stage 7), done
- `IsClosed.csInf_mem` (`Mathlib/Topology/Order/Monotone.lean`): a closed, nonempty, bounded-below set of reals contains its inf. In closed Case A this replaces the open case's "c ∉ S" argument.
- `closure_Ico (hab : a ≠ b) : closure (Ico a b) = Icc a b` and `closure_minimal` give "V_k closed, [0, c) ⊆ preimage ⇒ c ∈ preimage".
- `isClosed_biInter` for V_σ closed (our wrapper `isClosed_interU`; named with a `U` suffix to avoid a clash with any root name).
- `exists_lowest` from Case B works unchanged with F = V_i ∩ V_j (already closed, no closure needed). Closed Case B uses `Convex.openSegment_subset` instead of Rockafellar 6.1.
- Mathlib's `show` linter complains when `show` changes the goal (e.g. unfolding `t ∈ f ⁻¹' s` to `f t ∈ s`); use `change`.

## Stage 8 (70 codes, links), done
- **Kernel cost of Finset operations.** These are fine in `decide +kernel`: filters over `Finset.univ : Finset (Finset (Fin 7))` (128 sets), membership, `⊆`, `Disjoint`, `card`, `erase`, and Finset literals of about 26 codewords. This is very slow: quantifying over `(maximal C).powerset` and taking `F.inf id` (more than 300 s for one code, though each piece alone is fast). Avoid powerset/inf in anything the kernel evaluates; use `hull C σ = univ.filter (fun x => ∀ M ∈ maximal C, σ ⊆ M → x ∈ M)` instead.
- **Instance search limit.** `Decidable` of a large `A ∧ B` failed even though `Decidable A` and `Decidable B` were each found. Fix: name the two halves as separate defs, give each an instance, and build the conjunction with `inferInstanceAs`.
- **Recursive `Decidable` instance** for `CollapsesTo` (defined by pattern matching on the step list): write `instance decCollapsesTo : ∀ K steps L, Decidable (...)` by the same pattern match, using `have := decCollapsesTo ...` for the recursive call. The kernel reduces it fine.
- **Lemmas used:** `Finset.le_inf`, `Finset.inf_le` (Finset ≤ is ⊆), `Finset.singleton_subset_iff`, `Finset.exists_max_image`, `Finset.eq_of_subset_of_card_le`.
- **Memory:** four Lean processes doing heavy `decide +kernel` at once crashed on this 8 GB PC (exit code 0xC0000409, no message). Chaining the chunk files by imports limits it to two at once.
- **The JSON's "780 faces"** counts (family, face) pairs; there are 278 distinct faces.
- **Writing Python from the Bash tool:** `\n` inside a quoted heredoc sometimes reached the file as a real newline and broke string literals. Edit the generator with the Edit tool instead.

## Stage 9 (every missing face, one cited fact), done
- **Route chosen: a general cone lemma, not 1,132 more certificates.** The 278 certificates already take about 14 min (Links1 335 s + Links2 515 s); the skipped faces are smaller faces with bigger links, so certificates for them would cost far more. Instead `collapsible_of_cone` (`RimRule/LocallyGood.lean`) proves once that any cone complex collapses to its apex, and `collapsible_link_of_hull_ne` shows a face with `hull C σ ≠ σ` has a cone link. The certificates are unchanged.
- **Cone proof:** strong induction on `K` (`Finset.strongInduction`). Pick a largest nonempty face τ without the apex v (`Finset.exists_max_image`); `(τ, insert v τ)` is free because any ρ ⊋ τ either lacks v (too big) or has `ρ.erase v = τ` by maximality. After removing the pair, `K'` is still a complex containing ∅ and a cone. When no such τ is left, `K = {∅, {v}}`.
- Lemma names in this mathlib: `card_insert_of_notMem`, `notMem_erase`, `exists_of_ssubset`, `ssubset_iff_of_subset`, `HasSSubset.SSubset.trans_subset`, `HasSubset.Subset.ssubset_of_ne`. `Finset.exists_max_image` takes the set explicitly (`exists_max_image _ card hS`), not via dot notation on the `Nonempty` proof.
- `all70.Nodup` and `IsNeuralCode` are cheap by `decide +kernel` (about 18 s together in a scratch test).
- Python check (scratch script): 1,410 nonempty faces of Δ(C) ∖ C across the 70 codes, 278 equal to their hull, 1,132 not. Matches DEF_CHECK.md.

## Stage 10a (geometric realization), done
- **Definition by support, not by union.** `realization K = {x | x ≥ 0, ∑ x = 1, supp x ∈ K}`. For a complex this equals the textbook `⋃_{σ ∈ K} conv {eᵢ}` (`realization_eq_iUnion_convexHull`), but the support form puts each point in exactly one open simplex, which should make 10c (the collapse map on the open simplex τ) easier.
- **mathlib's `stdSimplex` is deprecated** (since 2026-08-29, in favour of a `StdSimplex` type). Not used; the conditions are written out by hand.
- **Contractibility lemmas:** `Convex.contractibleSpace` and `StarConvex.contractibleSpace (h : StarConvex ℝ x s) (hne : s.Nonempty) : ContractibleSpace s` in `Mathlib/Analysis/Convex/Contractible.lean`. 10b can use the second directly.
- **Nonempty from contractible:** `ContractibleSpace.hequiv_unit X : Nonempty (X ≃ₕ Unit)`; `e.invFun ()` is a point.
- `rw [h] at hx` failed when `hx : ↑(e.invFun ()) ∈ S` and `e`'s type mentions `S` (motive not type correct). Fix: state `hx` with an explicit type, then `simp only [h, Set.mem_empty_iff_false] at hx`.
- `Set.mem_setOf_eq` is deprecated; use `Set.mem_ofPred_eq`.
- Center of mass: `Finset.centerMass_mem_convexHull` + `Finset.centerMass_eq_of_sum_1`, then `Finset.sum_apply`, `Pi.single_apply`, `mul_ite`, `Finset.sum_ite_eq`.
- `supp` is defined with `open Classical in` (real `≠ 0` isn't decidable); all proofs go through `mem_supp`, so no instance mismatch came up.

## Stage 10b–10e (cones, collapses, collapsible ⇒ contractible, literal locally good), done
- **Cones (10b):** mathlib's `StarConvex.contractibleSpace` does all the topology; we only show `|K|` is star-convex around `e_v` (support of `a e_v + b x` ⊆ `insert v (supp x)`).
- **Collapse map (10c):** `f_t(x) = x + t·m(x)·(|σ| e_w − 𝟙_σ)`, `m(x) = min_{i∈σ} x_i` (`Finset.inf'`). One formula on all of `|K|`: `m = 0` exactly where the map must be the identity, so no pasting lemma. Continuity: `Continuous.finset_inf'_apply`. Lemmas: `Finset.exists_mem_eq_inf'`, `Finset.inf'_le`, `Finset.le_inf'`, `Finset.exists_eq_insert_iff` (to write `τ = insert w σ`).
- **`open unitInterval` breaks variables named `σ`** (it is notation for `unitInterval.symm`). Write `unitInterval` in full instead.
- **`≃ₕ` notation** is not in scope by default; write `ContinuousMap.HomotopyEquiv X Y`.
- **Binder types:** in `∀ t x, (x : Fin n → ℝ) ∈ S → H (t, x) = x` the ascription fixes `x : Fin n → ℝ`; give binder types explicitly.
- **Homotopy equivalence:** `left_inv` via `ContinuousMap.Homotopic.symm ⟨{ toContinuousMap := …, map_zero_left, map_one_left }⟩`; `right_inv` by proving `r.comp i = ContinuousMap.id _` with `ext y : 2` and rewriting. Transfer: `ContinuousMap.HomotopyEquiv.contractibleSpace`, `HomotopyEquiv.trans`, `HomotopyEquiv.refl`.
- **σ ≠ ∅ in 10d** comes for free: `∅ ∈ {∅, {v}}` and collapses only remove faces (`collapsesTo_subset`).
- **Def 2.13–2.15 of 1912.00963 (v3)** were read from the arXiv HTML page; quoted in `Mandatory.lean`.
- **Memory:** a docstring edit in `Defs.lean` forces a full rebuild (~29 min one module at a time). With ~150 MB RAM free, parallel `lake build` fails with `failed to read file …olean.private`; build modules one at a time with `lake build <Module>` in import order.
- `gh run list --commit` needs the full SHA; use `gh run list --limit 1` right after the push.

## CI failure (2026-11-22), fixed
- **Symptom:** GitHub Actions "Lean Action CI" failed on the Stage 4 and Stage 5 pushes (runs 44981470885, 44982072987) after about 16 min.
- **The Lean build was fine.** The `leanprover/lean-action@v1` step (`lake build`) passed both times. The proofs were never the problem.
- **Exact error:** in the template's `leanprover-community/docgen-action@v1` step, doc-gen4 builds HTML docs for every dependency (5,482 targets, mostly mathlib). It ended with `error: resource exhausted (error code: 12, not enough memory)` on the `*:srcUri.github` targets (mathlib, batteries, aesop, Qq, importGraph, …), then `Process completed with exit code 1`. Before that, many `WARNING: Failed to calculate equational lemmas … maximum number of heartbeats` lines appeared, which are harmless.
- **Fix:** removed the docgen step from `.github/workflows/lean_action_ci.yml`, along with the `pages: write` / `id-token: write` permissions it needed. The repo is private and GitHub Pages is off (the API returns 404), so the docs had nowhere to deploy anyway. CI now runs only `lake build`. No `.lean` file changed.

## Ideas for later stages
- **Rockafellar 6.5 (Stage 3)** needs only the ⊇ direction, and it holds in any real topological vector space. Take w ∈ U ∩ V and x ∈ cl U ∩ cl V. Then [w, x) ⊆ U ∩ V by `Convex.openSegment_interior_closure_subset_interior` (applied to U and to V), and x is a limit of points of [w, x).
- **Case B lowest point:** instead of an affine height h on aff T, we could minimise the z-barycentric weight γ over the compact set {(α,β,γ) ∈ stdSimplex : αa+βb+γz ∈ cl W}. That avoids building h and may avoid needing non-degeneracy.

## Census (Stage 2)
- Use `decide +kernel`, not plain `decide`. On 033, which has 13 codewords over `Fin 7`, plain `decide` fails with "maximum recursion depth has been reached", because the elaborator evaluates the `Decidable` instance. `decide +kernel` skips that and lets the kernel check the result. It adds no axiom (`#print axioms` stays clean), and each check takes a few seconds.
- `Fin.Nonempty` goals like `({4} : Finset (Fin 7)).Nonempty` are easiest as `⟨4, by decide⟩`.
- With `{ R with m := ∅ }` record updates, `decide +kernel` still evaluates fine.

## Dead ends
- Plain `decide` on the full 033 code (recursion depth). Use `decide +kernel`.
