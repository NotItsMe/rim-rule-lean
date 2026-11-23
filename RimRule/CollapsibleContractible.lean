import RimRule.Collapse

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Collapsible ⇒ contractible (Stage 10d)

`contractibleSpace_realization_of_collapsible`: if `K` is a simplicial complex and
`Collapsible K` (a list of elementary collapses takes `K` to a single vertex `{∅, {v}}`),
then the geometric realization `|K|` is contractible.

This is the fact that Stages 8–9 cited without proof ("collapsible ⇒ contractible"). The proof
is induction on the list of collapses:

* each elementary collapse `K ↘ K'` gives a homotopy equivalence `|K| ≃ₕ |K'|`
  (`realizationCollapseHEquiv`, Stage 10c), provided the free face is nonempty;
* the free face is nonempty because the final complex `{∅, {v}}` still contains `∅`, and a
  collapse never adds faces (`collapsesTo_subset`), so `∅` is never removed;
* the end point `|{∅, {v}}|` is a single point (`realization_vertex`, Stage 10a), which is
  contractible, and contractibility passes back along homotopy equivalences
  (mathlib's `ContinuousMap.HomotopyEquiv.contractibleSpace`).

Each intermediate complex is again a complex (`isComplex_elemCollapse`), which 10c needs.
-/

namespace RimRule

open Finset

variable {n : ℕ}

/-- In a free pair, `σ ⊊ τ`. -/
theorem ssubset_of_isFreeFace {K : Finset (Finset (Fin n))} {σ τ : Finset (Fin n)}
    (hf : IsFreeFace K σ τ) : σ ⊂ τ :=
  hf.2.2.1.ssubset_of_ne fun h => by
    have := hf.2.2.2.1
    rw [h] at this
    omega

/-- An elementary collapse of a complex is a complex. -/
theorem isComplex_elemCollapse {K : Finset (Finset (Fin n))} {σ τ : Finset (Fin n)}
    (hK : IsComplex K) (hf : IsFreeFace K σ τ) : IsComplex (elemCollapse K σ τ) := by
  intro ρ hρ ρ' hρ'
  obtain ⟨hρτ, hρσ, hρK⟩ := mem_elemCollapse.1 hρ
  refine mem_elemCollapse.2 ⟨?_, ?_, hK ρ hρK ρ' hρ'⟩
  · rintro rfl
    exact hρτ (hf.2.2.2.2 ρ hρK ((ssubset_of_isFreeFace hf).trans_subset hρ'))
  · rintro rfl
    exact hρτ (hf.2.2.2.2 ρ hρK (hρ'.ssubset_of_ne (Ne.symm hρσ)))

/-- Collapsing only removes faces. -/
theorem collapsesTo_subset : ∀ {K : Finset (Finset (Fin n))}
    {steps : List (Finset (Fin n) × Finset (Fin n))} {L : Finset (Finset (Fin n))},
    CollapsesTo K steps L → L ⊆ K
  | _, [], _, h => by
    change _ = _ at h
    rw [h]
  | K, (σ, τ) :: _, _, h => (collapsesTo_subset h.2).trans (elemCollapse_subset K σ τ)

/-- **A sequence of collapses is a homotopy equivalence.** If `K` is a complex, `steps`
collapses `K` to `L`, and `∅ ∈ L`, then `|K| ≃ₕ |L|`. -/
theorem nonempty_hequiv_of_collapsesTo : ∀ (K : Finset (Finset (Fin n)))
    (steps : List (Finset (Fin n) × Finset (Fin n))) (L : Finset (Finset (Fin n))),
    IsComplex K → CollapsesTo K steps L → ∅ ∈ L →
      Nonempty (ContinuousMap.HomotopyEquiv (realization K) (realization L))
  | K, [], L, _, h, _ => by
    change K = L at h
    subst h
    exact ⟨ContinuousMap.HomotopyEquiv.refl _⟩
  | K, (σ, τ) :: steps, L, hK, h, h0 => by
    obtain ⟨hf, hrest⟩ := h
    have h0' : ∅ ∈ elemCollapse K σ τ := collapsesTo_subset hrest h0
    have hσ : σ.Nonempty :=
      nonempty_iff_ne_empty.2 fun hσ => (mem_elemCollapse.1 h0').2.1 hσ.symm
    obtain ⟨e⟩ := nonempty_hequiv_of_collapsesTo _ steps L (isComplex_elemCollapse hK hf) hrest h0
    exact ⟨(realizationCollapseHEquiv hK hf hσ).trans e⟩

/-- **Collapsible ⇒ contractible.** If `K` is a simplicial complex that collapses to a single
vertex, its geometric realization `|K|` is contractible. -/
theorem contractibleSpace_realization_of_collapsible {K : Finset (Finset (Fin n))}
    (hK : IsComplex K) (h : Collapsible K) : ContractibleSpace (realization K) := by
  obtain ⟨steps, v, hs⟩ := h
  obtain ⟨e⟩ := nonempty_hequiv_of_collapsesTo K steps _ hK hs (mem_insert_self _ _)
  have := contractibleSpace_realization_vertex v
  exact e.contractibleSpace

/-- A collapsible link `lk_σ(Δ(C))` is contractible. -/
theorem contractibleSpace_realization_link_of_collapsible {C : Finset (Finset (Fin n))}
    {σ : Finset (Fin n)} (h : Collapsible (link (delta C) σ)) :
    ContractibleSpace (realization (link (delta C) σ)) :=
  contractibleSpace_realization_of_collapsible (isComplex_link (isComplex_delta C) σ) h

end RimRule
