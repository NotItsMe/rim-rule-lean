# NOTES: math and formalization decisions

## Conventions (Stage 1)
- **Neurons** are `Fin n`, so labels are 0-based. For readability in the census, use `Fin (n+1)` and leave 0 unused, so the paper's labels 1..n stay as they are.
- **Codes** are `Finset (Finset (Fin n))`, which makes every hypothesis decidable. A realization's code is a `Set`, and `IsRealization` says the two are equal via the coercion.
- **ℝ^d** is `Fin d → ℝ`, not `EuclideanSpace ℝ (Fin d)`. The topology and convexity are the same, and the import is much lighter. The definitions (`codeword`, `inter`, `codeOf`, `IsRealization`) are generic over any type `E`, so later proofs can work in any real topological vector space and then specialise.
- **Stimulus space X** is arbitrary (Chan Def 2.4), with U_s ⊆ X. This is the paper's general version and is stronger than the X = ℝ^d simplification the brief allows. Cost: when we read c(x) we must know x ∈ X. Every such point lies in some U_s with s in a nonempty role (σ_i, σ_j, or σ_m in open Case B), as in referee fix 3.
- **∅ ∈ C** is *not* assumed in `Theorem1a/1b`. That makes them stronger statements. `IsNeuralCode` is still defined, to mirror the paper.
- **σ_i ≠ ∅** is kept as a hypothesis, as in the paper. Referee fix 8 says it could be dropped, but that's optional.
- "Contains t" means `R.t ⊆ c`. Unions of roles are `Finset` unions, e.g. H5′ is `R.i ∪ R.m ∪ R.p ⊆ c ∧ ¬ R.j ⊆ c`.
- `Theorem1b` doesn't add "therefore not closed-convex". That follows from 1(a) and H4 ⇒ F_B, and can be a corollary later.

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

## Ideas for later stages
- **Rockafellar 6.5 (Stage 3)** needs only the ⊇ direction, and it holds in any real topological vector space. Take w ∈ U ∩ V and x ∈ cl U ∩ cl V. Then [w, x) ⊆ U ∩ V by `Convex.openSegment_interior_closure_subset_interior` (applied to U and to V), and x is a limit of points of [w, x).
- **Case B lowest point:** instead of an affine height h on aff T, we could minimise the z-barycentric weight γ over the compact set {(α,β,γ) ∈ stdSimplex : αa+βb+γz ∈ cl W}. That avoids building h and may avoid needing non-degeneracy.

## Census (Stage 2)
- Use `decide +kernel`, not plain `decide`. On 033, which has 13 codewords over `Fin 7`, plain `decide` fails with "maximum recursion depth has been reached", because the elaborator evaluates the `Decidable` instance. `decide +kernel` skips that and lets the kernel check the result. It adds no axiom (`#print axioms` stays clean), and each check takes a few seconds.
- `Fin.Nonempty` goals like `({4} : Finset (Fin 7)).Nonempty` are easiest as `⟨4, by decide⟩`.
- With `{ R with m := ∅ }` record updates, `decide +kernel` still evaluates fine.

## Dead ends
- Plain `decide` on the full 033 code (recursion depth). Use `decide +kernel`.
