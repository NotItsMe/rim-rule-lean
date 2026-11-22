import Mathlib.Analysis.Convex.Topology

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Rockafellar, Convex Analysis, Theorem 6.5 (the special case we use)

Rockafellar 6.5 says: if `C₁, C₂` are convex and their relative interiors meet, then
`cl (C₁ ∩ C₂) = cl C₁ ∩ cl C₂`. mathlib does not have it. We need only the special case where
both sets are **open** (so relative interior = the set itself), and in the Rim rule proof only
the `⊇` direction is used:

> If `U, V` are open and convex and `U ∩ V ≠ ∅`, then `cl U ∩ cl V ⊆ cl (U ∩ V)`.

We prove it in any real topological vector space, then specialise to `ℝ^d = Fin d → ℝ`.

**Proof.** Take `w ∈ U ∩ V` and `x ∈ cl U ∩ cl V`. Rockafellar 6.1
(`Convex.openSegment_interior_closure_subset_interior`) puts the open segment `(w, x)` inside
`U` (because `w ∈ U = int U` and `x ∈ cl U`) and likewise inside `V`. So `(w, x) ⊆ U ∩ V`, and
`x` lies in the closure of `(w, x)` (`segment_subset_closure_openSegment`).
-/

namespace RimRule

open Set

section TVS

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Rockafellar 6.1 for an open convex set: the open segment from a point of `U` to a point of
`cl U` lies in `U`. -/
theorem openSegment_subset_of_isOpen_convex {U : Set E} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {w x : E} (hw : w ∈ U) (hx : x ∈ closure U) : openSegment ℝ w x ⊆ U := by
  have h := hUc.openSegment_interior_closure_subset_interior (hUo.interior_eq ▸ hw) hx
  rwa [hUo.interior_eq] at h

/-- **Rockafellar 6.5, the direction we use.** If `U, V` are open, convex and meet, then
`cl U ∩ cl V ⊆ cl (U ∩ V)`. -/
theorem closure_inter_closure_subset_closure_inter {U V : Set E}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hVo : IsOpen V) (hVc : Convex ℝ V)
    (hUV : (U ∩ V).Nonempty) : closure U ∩ closure V ⊆ closure (U ∩ V) := by
  rintro x ⟨hxU, hxV⟩
  obtain ⟨w, hwU, hwV⟩ := hUV
  have hseg : openSegment ℝ w x ⊆ U ∩ V := fun y hy =>
    ⟨openSegment_subset_of_isOpen_convex hUo hUc hwU hxU hy,
      openSegment_subset_of_isOpen_convex hVo hVc hwV hxV hy⟩
  exact closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ w x))

/-- **Rockafellar 6.5, open special case, full equality.** If `U, V` are open, convex and meet,
then `cl (U ∩ V) = cl U ∩ cl V`. -/
theorem closure_inter_eq_of_isOpen_convex {U V : Set E}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hVo : IsOpen V) (hVc : Convex ℝ V)
    (hUV : (U ∩ V).Nonempty) : closure (U ∩ V) = closure U ∩ closure V :=
  Subset.antisymm (closure_inter_subset_inter_closure U V)
    (closure_inter_closure_subset_closure_inter hUo hUc hVo hVc hUV)

end TVS

/-- The brief's statement, on `ℝ^d = Fin d → ℝ`: for open convex `U, V ⊆ ℝ^d` with
`U ∩ V ≠ ∅`, `closure (U ∩ V) = closure U ∩ closure V`. -/
theorem rockafellar_6_5 {d : ℕ} {U V : Set (Fin d → ℝ)}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hVo : IsOpen V) (hVc : Convex ℝ V)
    (hUV : (U ∩ V).Nonempty) : closure (U ∩ V) = closure U ∩ closure V :=
  closure_inter_eq_of_isOpen_convex hUo hUc hVo hVc hUV

end RimRule
