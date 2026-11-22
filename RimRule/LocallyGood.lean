import RimRule.Complex

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Locally good codes, up to one cited fact

`LocallyGoodC C` says: for **every** nonempty face `σ ∈ Δ(C)` that is not a codeword, the
link `lk_σ(Δ(C))` is collapsible. Unlike `LinksCollapsible`, it skips no faces.

## From `LocallyGoodC` to "locally good"

Gambacini, Jeffs, Macdonald, Shiu (arXiv 1912.00963), Def 2.14–2.15: a code `C` is
**locally good** if every nonempty `σ ∈ Δ(C)` whose link `Lk_σ(Δ(C))` is not contractible
is a codeword. Equivalently: every nonempty `σ ∈ Δ(C) ∖ C` has a contractible link.
`LocallyGoodC C` gives a collapsible link for each such `σ`, so
`LocallyGoodC C ⇒ C is locally good` uses exactly one fact that is **cited, not proved
here**:

* *Collapsible ⇒ contractible.* An elementary collapse is a deformation retraction, so a
  complex that collapses to a single vertex is contractible. This is a standard textbook fact
  of combinatorial topology. mathlib has no geometric realization of abstract simplicial
  complexes, so it cannot be stated here.

No other cited fact is needed. In particular, the step from Curto et al. (Cor 4.6 /
Lemma 1.4: faces that are not intersections of facets have cone links) is now **proved**
in Lean, for these complexes, as `collapsible_link_of_hull_ne` below.

## What is proved here

* `collapsible_of_cone`: a finite simplicial complex that is a cone with apex `v`
  (adding `v` to a face gives a face) collapses to the single vertex `{∅, {v}}`. Proof: remove
  the pair `(τ, τ ∪ {v})` for a largest nonempty face `τ` without `v`, and repeat.
* `collapsible_link_of_hull_ne`: if `σ ∈ Δ(C)` is not its own hull (some vertex
  `v ∉ σ` lies in every maximal codeword containing `σ`), then `lk_σ(Δ(C))` is a cone with
  apex `v`, hence collapsible.
* `locallyGoodC_of_certOK`: a certificate checked by `CertOK` (which covers the faces equal to
  their hull) gives `LocallyGoodC C`. The remaining faces are handled by the cone lemma.
-/

namespace RimRule

open Finset

variable {n : ℕ}

/-! ### Cones collapse to their apex -/

/-- `K` is a **cone with apex `v`**: adding `v` to any face of `K` gives a face of `K`. -/
def IsConeWith (K : Finset (Finset (Fin n))) (v : Fin n) : Prop :=
  ∀ τ ∈ K, insert v τ ∈ K

theorem mem_elemCollapse {K : Finset (Finset (Fin n))} {σ τ ρ : Finset (Fin n)} :
    ρ ∈ elemCollapse K σ τ ↔ ρ ≠ τ ∧ ρ ≠ σ ∧ ρ ∈ K := by
  unfold elemCollapse
  rw [mem_erase, mem_erase]

/-- In a cone with apex `v`, a largest face `τ` without `v` is free, with coface `τ ∪ {v}`. -/
theorem isFreeFace_of_cone {K : Finset (Finset (Fin n))} {v : Fin n} (hK : IsComplex K)
    (hc : IsConeWith K v) {τ : Finset (Fin n)} (hτ : τ ∈ K) (hv : v ∉ τ)
    (hmax : ∀ ρ ∈ K, v ∉ ρ → ρ.card ≤ τ.card) : IsFreeFace K τ (insert v τ) := by
  refine ⟨hτ, hc τ hτ, subset_insert v τ, card_insert_of_notMem hv, ?_⟩
  intro ρ hρ hτρ
  by_cases hvρ : v ∈ ρ
  · have h1 : τ ⊆ ρ.erase v := fun x hx =>
      mem_erase.2 ⟨fun h => hv (h ▸ hx), hτρ.subset hx⟩
    have h2 : ρ.erase v ∈ K := hK ρ hρ _ (erase_subset v ρ)
    have h3 : τ = ρ.erase v := eq_of_subset_of_card_le h1 (hmax _ h2 (notMem_erase v ρ))
    rw [h3, insert_erase hvρ]
  · exact absurd (card_lt_card hτρ) (not_lt.2 (hmax ρ hρ hvρ))

/-- **A cone collapses to its apex.** If `K` is a simplicial complex containing `∅` and `K`
is a cone with apex `v`, then a sequence of elementary collapses takes `K` to `{∅, {v}}`. -/
theorem collapsible_of_cone (v : Fin n) (K : Finset (Finset (Fin n))) :
    IsComplex K → ∅ ∈ K → IsConeWith K v →
      ∃ steps, CollapsesTo K steps {∅, {v}} := by
  induction K using Finset.strongInduction with
  | H K ih =>
  intro hK h0 hc
  by_cases hS : (K.filter fun τ => v ∉ τ ∧ τ.Nonempty).Nonempty
  · -- Collapse a largest nonempty face `τ` without `v` together with `τ ∪ {v}`.
    obtain ⟨τ, hτS, hmaxS⟩ := exists_max_image _ card hS
    obtain ⟨hτ, hv, hne⟩ := (mem_filter.1 hτS)
    have hmax : ∀ ρ ∈ K, v ∉ ρ → ρ.card ≤ τ.card := by
      intro ρ hρ hvρ
      rcases ρ.eq_empty_or_nonempty with rfl | hρne
      · simp
      · exact hmaxS ρ (mem_filter.2 ⟨hρ, hvρ, hρne⟩)
    have hfree := isFreeFace_of_cone hK hc hτ hv hmax
    have hup := hfree.2.2.2.2
    set K' := elemCollapse K τ (insert v τ) with hK'
    have hsub : K' ⊆ K := fun ρ hρ => (mem_elemCollapse.1 hρ).2.2
    have hτK' : τ ∉ K' := fun h => (mem_elemCollapse.1 h).2.1 rfl
    have hss : K' ⊂ K := (ssubset_iff_of_subset hsub).2 ⟨τ, hτ, hτK'⟩
    -- `K'` is again a complex containing `∅` and a cone with apex `v`.
    have hK'c : IsComplex K' := by
      intro ρ hρ ρ' hρ'
      obtain ⟨hρ1, hρ2, hρK⟩ := mem_elemCollapse.1 hρ
      refine mem_elemCollapse.2 ⟨?_, ?_, hK ρ hρK ρ' hρ'⟩
      · rintro rfl
        exact hρ1 (hup ρ hρK ((ssubset_insert hv).trans_subset hρ'))
      · rintro rfl
        exact hρ1 (hup ρ hρK (hρ'.ssubset_of_ne (Ne.symm hρ2)))
    have h0' : ∅ ∈ K' :=
      mem_elemCollapse.2 ⟨(insert_ne_empty v τ).symm, hne.ne_empty.symm, h0⟩
    have hc' : IsConeWith K' v := by
      intro ρ hρ
      obtain ⟨hρ1, hρ2, hρK⟩ := mem_elemCollapse.1 hρ
      refine mem_elemCollapse.2 ⟨?_, ?_, hc ρ hρK⟩
      · intro h
        by_cases hvρ : v ∈ ρ
        · exact hρ1 (by rwa [insert_eq_of_mem hvρ] at h)
        · exact hρ2 (by rw [← erase_insert hvρ, h, erase_insert hv])
      · intro h
        exact hv (h ▸ mem_insert_self v ρ)
    obtain ⟨steps, hsteps⟩ := ih K' hss hK'c h0' hc'
    exact ⟨(τ, insert v τ) :: steps, hfree, hsteps⟩
  · -- No nonempty face without `v` is left, so `K = {∅, {v}}`.
    refine ⟨[], ?_⟩
    change K = {∅, {v}}
    have hnone : ∀ ρ ∈ K, v ∉ ρ → ρ = ∅ := fun ρ hρ hvρ =>
      not_nonempty_iff_eq_empty.1 fun hne => hS ⟨ρ, mem_filter.2 ⟨hρ, hvρ, hne⟩⟩
    ext ρ
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hρ
      by_cases hvρ : v ∈ ρ
      · right
        have he : ρ.erase v = ∅ :=
          hnone _ (hK ρ hρ _ (erase_subset v ρ)) (notMem_erase v ρ)
        rw [← insert_erase hvρ, he]
        rfl
      · exact Or.inl (hnone ρ hρ hvρ)
    · rintro (rfl | rfl)
      · exact h0
      · simpa using hc ∅ h0

/-! ### Links in `Δ(C)` -/

theorem isComplex_link {K : Finset (Finset (Fin n))} (hK : IsComplex K) (σ : Finset (Fin n)) :
    IsComplex (link K σ) := by
  intro τ hτ τ' hτ'
  simp only [link, mem_filter] at hτ ⊢
  obtain ⟨hτK, hd, hu⟩ := hτ
  exact ⟨hK τ hτK τ' hτ', hd.mono_left hτ', hK _ hu _ (union_subset_union hτ' subset_rfl)⟩

theorem empty_mem_link {K : Finset (Finset (Fin n))} (hK : IsComplex K) {σ : Finset (Fin n)}
    (hσ : σ ∈ K) : ∅ ∈ link K σ := by
  simp only [link, mem_filter, empty_union]
  exact ⟨hK σ hσ ∅ (empty_subset _), disjoint_empty_left _, hσ⟩

theorem subset_hull {C : Finset (Finset (Fin n))} {σ : Finset (Fin n)} : σ ⊆ hull C σ := by
  intro x hx
  simp only [hull, mem_filter, mem_univ, true_and]
  exact fun M _ hM => hM hx

/-- If `v ∉ σ` lies in every maximal codeword containing `σ`, then `lk_σ(Δ(C))` is a cone with
apex `v`. -/
theorem isConeWith_link_delta {C : Finset (Finset (Fin n))} {σ : Finset (Fin n)} {v : Fin n}
    (hv : v ∈ hull C σ) (hvσ : v ∉ σ) : IsConeWith (link (delta C) σ) v := by
  intro τ hτ
  rw [link_delta_eq] at hτ ⊢
  simp only [linkDelta, mem_filter, mem_univ, true_and] at hτ ⊢
  obtain ⟨hd, c, hc, hsub⟩ := hτ
  obtain ⟨M, hM, hcM⟩ := exists_maximal_above hc
  have hvM : v ∈ M := by
    simp only [hull, mem_filter, mem_univ, true_and] at hv
    exact hv M hM (subset_union_right.trans (hsub.trans hcM))
  refine ⟨disjoint_insert_left.2 ⟨hvσ, hd⟩, M, (mem_filter.1 hM).1, ?_⟩
  rw [insert_union]
  exact insert_subset hvM (hsub.trans hcM)

/-- **Faces that are not their own hull have collapsible links** (the Curto et al. Cor 4.6
step, proved). If `σ ∈ Δ(C)` and `hull C σ ≠ σ`, pick `v ∈ hull C σ ∖ σ`; the link is a cone
with apex `v`, so it collapses to `{∅, {v}}`. -/
theorem collapsible_link_of_hull_ne {C : Finset (Finset (Fin n))} {σ : Finset (Fin n)}
    (hΔ : σ ∈ delta C) (h : hull C σ ≠ σ) : Collapsible (link (delta C) σ) := by
  obtain ⟨v, hv, hvσ⟩ := exists_of_ssubset (subset_hull.ssubset_of_ne (Ne.symm h))
  obtain ⟨steps, hs⟩ := collapsible_of_cone v _ (isComplex_link (isComplex_delta C) σ)
    (empty_mem_link (isComplex_delta C) hΔ) (isConeWith_link_delta hv hvσ)
  exact ⟨steps, v, hs⟩

/-! ### Locally good, up to collapsible ⇒ contractible -/

/-- **`LocallyGoodC C`**: every nonempty face `σ ∈ Δ(C)` that is not a codeword has a
collapsible link `lk_σ(Δ(C))`.

This implies that `C` is **locally good** in the sense of Gambacini, Jeffs, Macdonald, Shiu
(arXiv 1912.00963, Def 2.14–2.15: every nonempty `σ ∈ Δ(C)` with non-contractible link is a
codeword) via the single cited fact **collapsible ⇒ contractible**, which is not proved here
(see the module doc). -/
def LocallyGoodC (C : Finset (Finset (Fin n))) : Prop :=
  ∀ σ ∈ delta C, σ.Nonempty → σ ∉ C → Collapsible (link (delta C) σ)

/-- `LocallyGoodC` is stronger than `LinksCollapsible` (which only asks about faces that are
intersections of maximal codewords). -/
theorem LocallyGoodC.linksCollapsible {C : Finset (Finset (Fin n))} (h : LocallyGoodC C) :
    LinksCollapsible C :=
  fun σ hΔ hne _ hnot => h σ hΔ hne hnot

/-- A checked certificate gives `LocallyGoodC C`. Faces equal to their hull are covered by the
certificate; every other face has a cone link (`collapsible_link_of_hull_ne`). -/
theorem locallyGoodC_of_certOK {C : Finset (Finset (Fin n))} {cert : List (LinkCert n)}
    (h : CertOK C cert) : LocallyGoodC C := by
  intro σ hΔ hne hnot
  by_cases hh : hull C σ = σ
  · obtain ⟨e, he, hσ⟩ := h.1 σ hΔ hne hnot hh
    have := h.2 e he
    rw [hσ] at this
    rw [link_delta_eq]
    exact ⟨_, _, this⟩
  · exact collapsible_link_of_hull_ne hΔ hh

end RimRule
