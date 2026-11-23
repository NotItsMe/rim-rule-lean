import RimRule.Realization
import RimRule.LocallyGood

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# An elementary collapse is a deformation retraction (Stage 10c)

Let `K` be a complex and `(σ, τ)` a free pair of `K` (`IsFreeFace K σ τ`) with `σ ≠ ∅`.
Write `τ = σ ∪ {w}` with `w ∉ σ`, and `K' = elemCollapse K σ τ = K ∖ {σ, τ}`. We prove that
`|K|` **deformation retracts onto** `|K'|` (`realization_deformationRetract`), and hence that
`|K|` and `|K'|` are homotopy equivalent (`realizationCollapseHEquiv`).

## Definition mirrored

Hatcher, *Algebraic Topology* (2002), Ch. 0, p. 2: "A *deformation retraction* of a space `X`
onto a subspace `A` is a family of maps `f_t : X → X`, `t ∈ I`, such that `f_0 = 𝟙` (the
identity map), `f_1(X) = A`, and `f_t | A = 𝟙` for all `t`. The family `f_t` should be
continuous in the sense that the associated map `X × I → X`, `(x, t) ↦ f_t(x)`, is
continuous." (Quoted from memory; check against a copy.) `realization_deformationRetract`
states exactly this, with `f_1(X) ⊆ A` (which, with `f_t | A = 𝟙`, gives `f_1(X) = A`).

## The map

For `x ∈ |K|` let `m(x) = min_{i ∈ σ} x i` (`minOn`) and let `d = |σ| e_w − 𝟙_σ` (`pushDir`).
The homotopy is the straight line

  `f_t(x) = x + (t · m(x)) • d`     (`pushAlong`).

* If `m(x) = 0` (some coordinate of `σ` vanishes, i.e. `x` is already in `|K'|` or outside the
  open star of `σ`), then `f_t(x) = x`.
* If `m(x) > 0`, the support of `x` contains `σ`, so (by freeness) it is `σ` or `τ`, and `x`
  lies in the closed simplex `|τ|`. Then `f_t` subtracts `t m(x)` from each `σ`-coordinate and
  adds `|σ| t m(x)` to the `w`-coordinate: the sum stays `1`, the coordinates stay `≥ 0`, and the
  support stays inside `τ`. At `t = 1` the smallest `σ`-coordinate becomes `0`, so `f_1(x)` lies
  on a face of `τ` not containing `σ`, which is in `K'`.

This is the usual "push the open simplex `τ` away from the free face `σ`" map (the standard
proof that an elementary collapse is a deformation retraction; see e.g. Cohen, *A Course in
Simple-Homotopy Theory*, Ch. II, or Kozlov, *Combinatorial Algebraic Topology*, the chapter
on simplicial collapses; chapter numbers cited from memory). Here it is a single formula on
all of `|K|`, so no pasting lemma is needed: `m` is continuous (a finite minimum of
coordinates) and vanishes wherever the map should be the identity.

`σ ≠ ∅` is needed: if `σ = ∅` then `K = {∅, {w}}`, `|K|` is a point and `|K'| = ∅`.
-/

namespace RimRule

open Finset

variable {n : ℕ}

/-! ### The push map -/

/-- `m(x) = min_{i ∈ σ} x i`. -/
noncomputable def minOn (σ : Finset (Fin n)) (hσ : σ.Nonempty) (x : Fin n → ℝ) : ℝ :=
  σ.inf' hσ fun i => x i

/-- The push direction `d = |σ| e_w − 𝟙_σ`. -/
noncomputable def pushDir (σ : Finset (Fin n)) (w : Fin n) : Fin n → ℝ :=
  fun i => (if i = w then (σ.card : ℝ) else 0) - (if i ∈ σ then 1 else 0)

/-- The straight-line homotopy `f_t(x) = x + (t · m(x)) • d`. -/
noncomputable def pushAlong (σ : Finset (Fin n)) (hσ : σ.Nonempty) (w : Fin n) (t : ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  x + (t * minOn σ hσ x) • pushDir σ w

section push

variable {σ : Finset (Fin n)} (hσ : σ.Nonempty) {w : Fin n}

theorem continuous_minOn : Continuous (minOn σ hσ) :=
  Continuous.finset_inf'_apply hσ fun i _ => continuous_apply i

theorem continuous_pushAlong :
    Continuous fun p : ℝ × (Fin n → ℝ) => pushAlong σ hσ w p.1 p.2 :=
  continuous_snd.add
    ((continuous_fst.mul ((continuous_minOn hσ).comp continuous_snd)).smul continuous_const)

theorem minOn_le {x : Fin n → ℝ} {i : Fin n} (hi : i ∈ σ) : minOn σ hσ x ≤ x i :=
  inf'_le (fun i => x i) hi

theorem exists_eq_minOn (x : Fin n → ℝ) : ∃ i ∈ σ, minOn σ hσ x = x i :=
  exists_mem_eq_inf' hσ fun i => x i

theorem minOn_nonneg {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ minOn σ hσ x :=
  le_inf' hσ _ fun i _ => hx i

theorem pushAlong_apply (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    pushAlong σ hσ w t x i = x i + t * minOn σ hσ x * pushDir σ w i := by
  simp [pushAlong]

theorem pushAlong_zero (x : Fin n → ℝ) : pushAlong σ hσ w 0 x = x := by
  simp [pushAlong]

theorem pushAlong_of_minOn_eq_zero {x : Fin n → ℝ} (h : minOn σ hσ x = 0) (t : ℝ) :
    pushAlong σ hσ w t x = x := by
  simp [pushAlong, h]

theorem pushDir_of_mem (hw : w ∉ σ) {i : Fin n} (hi : i ∈ σ) : pushDir σ w i = -1 := by
  have : i ≠ w := fun h => hw (h ▸ hi)
  simp [pushDir, this, hi]

theorem pushDir_of_notMem {i : Fin n} (hi : i ∉ σ) : 0 ≤ pushDir σ w i := by
  unfold pushDir
  split_ifs <;> simp_all

theorem pushDir_of_notMem_insert {i : Fin n} (hi : i ∉ insert w σ) : pushDir σ w i = 0 := by
  rw [mem_insert, not_or] at hi
  simp [pushDir, hi.1, hi.2]

theorem sum_pushDir (w : Fin n) : ∑ i, pushDir σ w i = 0 := by
  simp [pushDir, sum_sub_distrib]

end push

/-! ### Free pairs -/

/-- In a free pair `(σ, τ)`, a face containing `σ` is `σ` or `τ`. -/
theorem eq_or_eq_of_isFreeFace {K : Finset (Finset (Fin n))} {σ τ ρ : Finset (Fin n)}
    (hf : IsFreeFace K σ τ) (hρ : ρ ∈ K) (hσρ : σ ⊆ ρ) : ρ = σ ∨ ρ = τ := by
  by_cases h : σ = ρ
  · exact Or.inl h.symm
  · exact Or.inr (hf.2.2.2.2 ρ hρ (hσρ.ssubset_of_ne h))

/-- The coface of a free face adds one vertex: `τ = insert w σ` with `w ∉ σ`. -/
theorem exists_insert_of_isFreeFace {K : Finset (Finset (Fin n))} {σ τ : Finset (Fin n)}
    (hf : IsFreeFace K σ τ) : ∃ w ∉ σ, insert w σ = τ :=
  exists_eq_insert_iff.2 ⟨hf.2.2.1, hf.2.2.2.1.symm⟩

/-- A face of `K` that does not contain `σ` survives the collapse. -/
theorem mem_elemCollapse_of_not_subset {K : Finset (Finset (Fin n))} {σ τ ρ : Finset (Fin n)}
    (hf : IsFreeFace K σ τ) (hρ : ρ ∈ K) (hσρ : ¬ σ ⊆ ρ) : ρ ∈ elemCollapse K σ τ := by
  refine mem_elemCollapse.2 ⟨?_, ?_, hρ⟩
  · rintro rfl; exact hσρ hf.2.2.1
  · rintro rfl; exact hσρ subset_rfl

theorem realization_mono {K L : Finset (Finset (Fin n))} (h : K ⊆ L) :
    realization K ⊆ realization L :=
  fun _ ⟨h0, h1, h2⟩ => ⟨h0, h1, h h2⟩

theorem elemCollapse_subset (K : Finset (Finset (Fin n))) (σ τ : Finset (Fin n)) :
    elemCollapse K σ τ ⊆ K :=
  fun _ h => (mem_elemCollapse.1 h).2.2

/-! ### The homotopy stays in `|K|`, ends in `|K'|`, and fixes `|K'|` -/

section collapse

variable {K : Finset (Finset (Fin n))} {σ τ : Finset (Fin n)} {w : Fin n}
  (hK : IsComplex K) (hf : IsFreeFace K σ τ) (hσ : σ.Nonempty) (hw : w ∉ σ)
  (hτ : insert w σ = τ)
include hK hf hw hτ

omit hK hw hτ in
/-- If `m(x) > 0` then `x` lies in the closed simplex `τ`. -/
theorem supp_subset_of_minOn_pos {x : Fin n → ℝ} (hx : x ∈ realization K)
    (hm : 0 < minOn σ hσ x) : supp x ⊆ τ := by
  have hσx : σ ⊆ supp x := fun i hi => mem_supp.2 (ne_of_gt (hm.trans_le (minOn_le hσ hi)))
  rcases eq_or_eq_of_isFreeFace hf hx.2.2 hσx with h | h
  · rw [h]; exact hf.2.2.1
  · rw [h]

/-- `f_t(x) ∈ |K|` for `x ∈ |K|` and `t ∈ [0, 1]`. -/
theorem pushAlong_mem {x : Fin n → ℝ} (hx : x ∈ realization K) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : pushAlong σ hσ w t x ∈ realization K := by
  obtain ⟨hx0, hx1, hxK⟩ := hx
  have hm0 := minOn_nonneg hσ hx0
  rcases hm0.lt_or_eq with hm | hm
  · have hsupp := supp_subset_of_minOn_pos hf hσ ⟨hx0, hx1, hxK⟩ hm
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rw [pushAlong_apply]
      by_cases hi : i ∈ σ
      · rw [pushDir_of_mem hw hi]
        have h1 : minOn σ hσ x ≤ x i := minOn_le hσ hi
        have h2 : t * minOn σ hσ x ≤ minOn σ hσ x := mul_le_of_le_one_left hm0 ht1
        linarith
      · exact add_nonneg (hx0 i)
          (mul_nonneg (mul_nonneg ht0 hm0) (pushDir_of_notMem hi))
    · simp only [pushAlong_apply]
      rw [sum_add_distrib, ← mul_sum, sum_pushDir, mul_zero, add_zero, hx1]
    · refine hK τ hf.2.1 _ fun i hi => ?_
      rw [mem_supp, pushAlong_apply] at hi
      by_contra hiτ
      rw [← hτ] at hiτ
      have hxi : x i = 0 := by
        by_contra h
        exact hiτ (hτ ▸ hsupp (mem_supp.2 h))
      rw [hxi, pushDir_of_notMem_insert hiτ] at hi
      simp at hi
  · rw [pushAlong_of_minOn_eq_zero hσ hm.symm]
    exact ⟨hx0, hx1, hxK⟩

/-- `f_1(x) ∈ |K'|` for `x ∈ |K|`: the smallest `σ`-coordinate of `f_1(x)` is `0`. -/
theorem pushAlong_one_mem {x : Fin n → ℝ} (hx : x ∈ realization K) :
    pushAlong σ hσ w 1 x ∈ realization (elemCollapse K σ τ) := by
  obtain ⟨h0, h1, hK'⟩ := pushAlong_mem hK hf hσ hw hτ hx zero_le_one le_rfl
  refine ⟨h0, h1, mem_elemCollapse_of_not_subset hf hK' fun hsub => ?_⟩
  obtain ⟨i, hi, hmi⟩ := exists_eq_minOn hσ x
  have := mem_supp.1 (hsub hi)
  rw [pushAlong_apply, pushDir_of_mem hw hi, ← hmi] at this
  exact this (by ring)

omit hK hw hτ in
/-- `f_t` is the identity on `|K'|`. -/
theorem pushAlong_of_mem_elemCollapse {x : Fin n → ℝ}
    (hx : x ∈ realization (elemCollapse K σ τ)) (t : ℝ) : pushAlong σ hσ w t x = x := by
  obtain ⟨hx0, -, hxK'⟩ := hx
  obtain ⟨hne1, hne2, hxK⟩ := mem_elemCollapse.1 hxK'
  refine pushAlong_of_minOn_eq_zero hσ ?_ t
  by_contra hm
  have hm' : 0 < minOn σ hσ x := (minOn_nonneg hσ hx0).lt_of_ne (Ne.symm hm)
  have hσx : σ ⊆ supp x := fun i hi => mem_supp.2 (ne_of_gt (hm'.trans_le (minOn_le hσ hi)))
  rcases eq_or_eq_of_isFreeFace hf hxK hσx with h | h
  · exact hne2 h
  · exact hne1 h

end collapse

/-! ### The deformation retraction and the homotopy equivalence -/

section main

variable {K : Finset (Finset (Fin n))} {σ τ : Finset (Fin n)}

/-- The homotopy `I × |K| → |K|`, `(t, x) ↦ f_t(x)`. -/
noncomputable def pushHomotopyMap (hK : IsComplex K) (hf : IsFreeFace K σ τ) (hσ : σ.Nonempty)
    {w : Fin n} (hw : w ∉ σ) (hτ : insert w σ = τ) :
    C(unitInterval × realization K, realization K) where
  toFun p := ⟨pushAlong σ hσ w p.1 p.2, pushAlong_mem hK hf hσ hw hτ p.2.2 p.1.2.1 p.1.2.2⟩
  continuous_toFun :=
    ((continuous_pushAlong hσ).comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- **An elementary collapse is a deformation retraction** (Hatcher's definition, see the
module doc). If `K` is a complex and `(σ, τ)` is a free pair with `σ ≠ ∅`, there is a
continuous `H : I × |K| → |K|` with `H(0, x) = x`, `H(1, x) ∈ |K'|`, and `H(t, x) = x` for
every `t` and every `x ∈ |K'|`, where `K' = elemCollapse K σ τ`. -/
theorem realization_deformationRetract (hK : IsComplex K) (hf : IsFreeFace K σ τ)
    (hσ : σ.Nonempty) :
    ∃ H : C(unitInterval × realization K, realization K),
      (∀ x, H (0, x) = x) ∧
      (∀ x, (H (1, x) : Fin n → ℝ) ∈ realization (elemCollapse K σ τ)) ∧
      (∀ (t : unitInterval) (x : realization K),
        (x : Fin n → ℝ) ∈ realization (elemCollapse K σ τ) → H (t, x) = x) := by
  obtain ⟨w, hw, hτ⟩ := exists_insert_of_isFreeFace hf
  refine ⟨pushHomotopyMap hK hf hσ hw hτ, fun x => ?_, fun x => ?_, fun t x hx => ?_⟩
  · exact Subtype.ext (pushAlong_zero hσ x)
  · exact pushAlong_one_mem hK hf hσ hw hτ x.2
  · exact Subtype.ext (pushAlong_of_mem_elemCollapse hf hσ hx t)

/-- **`|K|` and `|K'|` are homotopy equivalent** for an elementary collapse `K ↘ K'` at a free
pair `(σ, τ)` with `σ ≠ ∅`. The maps are the retraction `f_1 : |K| → |K'|` and the inclusion
`|K'| → |K|`; `f_1 ∘ incl = 𝟙` exactly and `incl ∘ f_1 ≃ 𝟙` by the homotopy `f_t`. -/
noncomputable def realizationCollapseHEquiv (hK : IsComplex K) (hf : IsFreeFace K σ τ)
    (hσ : σ.Nonempty) :
    ContinuousMap.HomotopyEquiv (realization K) (realization (elemCollapse K σ τ)) :=
  let w := (exists_insert_of_isFreeFace hf).choose
  have hw : w ∉ σ := (exists_insert_of_isFreeFace hf).choose_spec.1
  have hτ : insert w σ = τ := (exists_insert_of_isFreeFace hf).choose_spec.2
  let r : C(realization K, realization (elemCollapse K σ τ)) :=
    ⟨fun x => ⟨pushAlong σ hσ w 1 x, pushAlong_one_mem hK hf hσ hw hτ x.2⟩,
      (((continuous_pushAlong hσ).comp (continuous_const.prodMk continuous_id)).comp
        continuous_subtype_val).subtype_mk _⟩
  let i : C(realization (elemCollapse K σ τ), realization K) :=
    ⟨fun y => ⟨y, realization_mono (elemCollapse_subset K σ τ) y.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  { toFun := r
    invFun := i
    left_inv := by
      refine ContinuousMap.Homotopic.symm ⟨?_⟩
      exact
        { toContinuousMap := pushHomotopyMap hK hf hσ hw hτ
          map_zero_left := fun x => Subtype.ext (pushAlong_zero hσ x)
          map_one_left := fun x => rfl }
    right_inv := by
      have : r.comp i = ContinuousMap.id _ := by
        ext y : 2
        exact pushAlong_of_mem_elemCollapse hf hσ y.2 1
      rw [this] }

/-- Non-constructive form of `realizationCollapseHEquiv`. -/
theorem nonempty_hequiv_realization_elemCollapse (hK : IsComplex K) (hf : IsFreeFace K σ τ)
    (hσ : σ.Nonempty) :
    Nonempty (ContinuousMap.HomotopyEquiv (realization K) (realization (elemCollapse K σ τ))) :=
  ⟨realizationCollapseHEquiv hK hf hσ⟩

end main

end RimRule
