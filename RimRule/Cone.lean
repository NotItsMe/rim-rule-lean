import RimRule.Realization
import RimRule.LocallyGood

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# The realization of a cone is contractible (Stage 10b)

`K` is a **cone with apex `v`** (`IsConeWith K v`, from `RimRule/LocallyGood.lean`) if adding
`v` to any face gives a face. Geometrically, `|K|` is then the union of the segments from the
apex vertex `e_v` to the points of `|K|`, so `|K|` is **star-convex** around `e_v`
(`starConvex_realization_cone`). A nonempty star-convex set is contractible (mathlib's
`StarConvex.contractibleSpace`, `Mathlib/Analysis/Convex/Contractible.lean`), which gives
`contractibleSpace_realization_cone`.

This is the textbook fact that a cone deformation retracts to its apex (Hatcher, *Algebraic
Topology*, Ch. 0, where the cone `CX` is introduced; cited from memory, check against a copy).
The segment from `e_v` to `x` stays in `|K|` because every point on it has support `supp x`,
`{v} ∪ supp x` or `{v}`, and these are faces of `K`.

As a corollary, `contractibleSpace_realization_link_of_hull_ne`: a face of `Δ(C)` that is not
its own hull has a contractible link (its link is a cone, `isConeWith_link_delta`).
-/

namespace RimRule

open Finset

variable {n : ℕ}

theorem vtx_mem_realization {K : Finset (Finset (Fin n))} {v : Fin n} (h : {v} ∈ K) :
    vtx v ∈ realization K :=
  ⟨vtx_nonneg v, sum_vtx v, by rw [supp_vtx]; exact h⟩

/-- A point on the segment from `e_v` to `x` has support inside `{v} ∪ supp x`. -/
theorem supp_smul_vtx_add_smul_subset (v : Fin n) (x : Fin n → ℝ) (a b : ℝ) :
    supp (a • vtx v + b • x) ⊆ insert v (supp x) := by
  intro i hi
  rw [mem_supp] at hi
  by_cases hiv : i = v
  · rw [hiv]; exact mem_insert_self v _
  · refine mem_insert_of_mem (mem_supp.2 fun hx => hi ?_)
    simp [vtx, hiv, hx]

/-- **A cone is star-convex around its apex.** If `K` is a complex and a cone with apex `v`,
then `|K|` is star-convex around the vertex `e_v`. -/
theorem starConvex_realization_cone {K : Finset (Finset (Fin n))} {v : Fin n}
    (hK : IsComplex K) (hc : IsConeWith K v) : StarConvex ℝ (vtx v) (realization K) := by
  rintro y ⟨hy0, hy1, hyK⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (vtx_nonneg v i)) (mul_nonneg hb (hy0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_vtx, hy1, mul_one, mul_one, hab]
  · exact hK _ (hc _ hyK) _ (supp_smul_vtx_add_smul_subset v y a b)

/-- **The realization of a cone is contractible.** If `K` is a complex containing `∅` and a
cone with apex `v`, then `|K|` is contractible. -/
theorem contractibleSpace_realization_cone {K : Finset (Finset (Fin n))} {v : Fin n}
    (hK : IsComplex K) (h0 : ∅ ∈ K) (hc : IsConeWith K v) :
    ContractibleSpace (realization K) :=
  (starConvex_realization_cone hK hc).contractibleSpace
    ⟨vtx v, vtx_mem_realization (by simpa using hc ∅ h0)⟩

/-- A face `σ ∈ Δ(C)` that is not its own hull has a **contractible** link: the link is a cone
(`isConeWith_link_delta`). -/
theorem contractibleSpace_realization_link_of_hull_ne {C : Finset (Finset (Fin n))}
    {σ : Finset (Fin n)} (hΔ : σ ∈ delta C) (h : hull C σ ≠ σ) :
    ContractibleSpace (realization (link (delta C) σ)) := by
  obtain ⟨v, hv, hvσ⟩ := exists_of_ssubset (subset_hull.ssubset_of_ne (Ne.symm h))
  exact contractibleSpace_realization_cone (isComplex_link (isComplex_delta C) σ)
    (empty_mem_link (isComplex_delta C) hΔ) (isConeWith_link_delta hv hvσ)

end RimRule
