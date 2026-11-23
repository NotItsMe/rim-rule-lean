import RimRule.Complex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Contractible

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Geometric realization of a finite simplicial complex (Stage 10a)

For a complex `K : Finset (Finset (Fin n))` on the vertex set `Fin n`, its **geometric
realization** `realization K ⊆ (Fin n → ℝ)` is the set of points `x` with

* `x i ≥ 0` for every `i`,
* `∑ i, x i = 1`, and
* the support `{i | x i ≠ 0}` is a face of `K`.

## The textbook definition this mirrors

Hatcher, *Algebraic Topology*, defines the standard simplex as
"Δⁿ = {(t₀, …, tₙ) ∈ ℝⁿ⁺¹ | Σᵢ tᵢ = 1 and tᵢ ≥ 0 for all i}", and calls the subsimplex spanned
by any nonempty subset of the vertices a *face*. The usual realization of an abstract
simplicial complex `K` on vertices `{1, …, n}` (Munkres, *Elements of Algebraic Topology*;
Matoušek, *Using the Borsuk–Ulam Theorem*) puts vertex `i` at the standard basis vector
`eᵢ` and takes

  `|K| = ⋃_{σ ∈ K} conv {eᵢ : i ∈ σ}`,

the union of the faces of the big simplex `Δⁿ⁻¹ ⊆ ℝⁿ` spanned by the faces of `K`.
`realization_eq_iUnion_convexHull` proves that our `realization K` is exactly this union
whenever `K` is closed under subsets (`IsComplex K`). Using the support instead of the union
is the same set, and it is easier to compute with: each point of `|K|` lies in the *open*
simplex of exactly one face, namely its support.

(The two quotations above were written from memory of the printed books; a human should
check the wording against a copy.)

## Sanity checks proved here

* `realization_singleton_empty`: `|{∅}| = ∅`. So `|{∅}|` is **not** contractible
  (`not_contractibleSpace_realization_singleton_empty`): a contractible space is nonempty.
  This matches the papers' convention that the link of a facet is `{∅}`, whose realization
  is empty, so every facet is a *mandatory* face (Gambacini–Jeffs–Macdonald–Shiu,
  arXiv 1912.00963, Def 2.14–2.15).
* `realization_vertex`: `|{∅, {v}}|` is the single point `e_v`; it is contractible.
* `realization_powerset`: the full simplex on `σ` (all subsets of `σ`) realizes as the face
  `{x ∈ Δⁿ⁻¹ | xᵢ = 0 for i ∉ σ}`; it equals `conv {eᵢ : i ∈ σ}`
  (`realization_powerset_eq_convexHull`), is convex, and is contractible when `σ ≠ ∅`
  (`contractibleSpace_realization_powerset`, from mathlib's `Convex.contractibleSpace`).
-/

namespace RimRule

open Finset

variable {n : ℕ}

/-! ### Definition -/

open Classical in
/-- The **support** of a point `x : Fin n → ℝ`: the coordinates where `x` is nonzero. -/
noncomputable def supp (x : Fin n → ℝ) : Finset (Fin n) :=
  univ.filter fun i => x i ≠ 0

@[simp] theorem mem_supp {x : Fin n → ℝ} {i : Fin n} : i ∈ supp x ↔ x i ≠ 0 := by
  classical
  simp [supp]

/-- The **geometric realization** `|K|` of `K : Finset (Finset (Fin n))` inside `Fin n → ℝ`:
points of the standard simplex (nonnegative coordinates summing to `1`) whose support is a
face of `K`. See the module docstring for the textbook definition this mirrors. -/
def realization (K : Finset (Finset (Fin n))) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 ∧ supp x ∈ K}

theorem mem_realization {K : Finset (Finset (Fin n))} {x : Fin n → ℝ} :
    x ∈ realization K ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 ∧ supp x ∈ K :=
  Iff.rfl

/-- The `i`-th vertex `eᵢ` of the standard simplex. -/
noncomputable abbrev vtx (i : Fin n) : Fin n → ℝ := Pi.single i 1

theorem supp_subset_iff {x : Fin n → ℝ} {σ : Finset (Fin n)} :
    supp x ⊆ σ ↔ ∀ i ∉ σ, x i = 0 := by
  constructor
  · intro h i hi
    by_contra hx
    exact hi (h (mem_supp.2 hx))
  · intro h i hi
    by_contra hiσ
    exact mem_supp.1 hi (h i hiσ)

/-- A point summing to `1` has nonempty support. -/
theorem supp_ne_empty {x : Fin n → ℝ} (hx : ∑ i, x i = 1) : supp x ≠ ∅ := by
  intro h
  have h0 : ∀ i, x i = 0 := fun i => by
    by_contra hi
    have : i ∈ supp x := mem_supp.2 hi
    rw [h] at this
    exact absurd this (notMem_empty i)
  simp [h0] at hx

theorem vtx_nonneg (v i : Fin n) : 0 ≤ vtx v i := by
  by_cases h : i = v
  · subst h; simp
  · simp [vtx, h]

theorem sum_vtx (v : Fin n) : ∑ i, vtx v i = 1 := by
  simp [vtx]

theorem supp_vtx (v : Fin n) : supp (vtx v) = {v} := by
  ext i
  by_cases h : i = v
  · subst h; simp
  · simp [vtx, h]

/-! ### `|{∅}| = ∅`, so it is not contractible -/

/-- `|{∅}| = ∅`: no point of the simplex has empty support. -/
theorem realization_singleton_empty :
    realization ({∅} : Finset (Finset (Fin n))) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, hsum, hK⟩
  exact supp_ne_empty hsum (mem_singleton.1 hK)

/-- `|{∅}|` is not contractible (a contractible space is nonempty). This is why the link
`{∅}` of a facet makes the facet a mandatory face. -/
theorem not_contractibleSpace_realization_singleton_empty :
    ¬ ContractibleSpace (realization ({∅} : Finset (Finset (Fin n)))) := by
  intro h
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit (realization ({∅} : Finset (Finset (Fin n))))
  have hx : ((e.invFun () : realization ({∅} : Finset (Finset (Fin n)))) : Fin n → ℝ) ∈
      realization ({∅} : Finset (Finset (Fin n))) := (e.invFun ()).2
  simp only [realization_singleton_empty, Set.mem_empty_iff_false] at hx

/-! ### `|{∅, {v}}|` is one point -/

/-- `|{∅, {v}}| = {e_v}`: a single vertex realizes as a single point. -/
theorem realization_vertex (v : Fin n) :
    realization ({∅, {v}} : Finset (Finset (Fin n))) = {vtx v} := by
  ext x
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hsum, hK⟩
    rcases mem_insert.1 hK with h | h
    · exact absurd h (supp_ne_empty hsum)
    · have hsv : supp x = {v} := mem_singleton.1 h
      have hz : ∀ i, i ≠ v → x i = 0 := fun i hi =>
        (supp_subset_iff.1 hsv.subset) i (by simpa using hi)
      have hv : x v = 1 := by
        rw [← hsum, Finset.sum_eq_single v (fun i _ hi => hz i hi) (by simp)]
      funext i
      by_cases h : i = v
      · subst h; simp [vtx, hv]
      · simp [vtx, h, hz i h]
  · rintro rfl
    exact ⟨vtx_nonneg v, sum_vtx v, by rw [supp_vtx]; simp⟩

theorem contractibleSpace_realization_vertex (v : Fin n) :
    ContractibleSpace (realization ({∅, {v}} : Finset (Finset (Fin n)))) := by
  rw [realization_vertex]
  have : Nonempty ({vtx v} : Set (Fin n → ℝ)) := ⟨⟨vtx v, rfl⟩⟩
  infer_instance

/-! ### The full simplex on `σ` -/

/-- The full simplex on `σ` (every subset of `σ`) realizes as the face of `Δⁿ⁻¹` spanned by
`σ`: points of the simplex vanishing off `σ`. -/
theorem realization_powerset (σ : Finset (Fin n)) :
    realization σ.powerset = {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 ∧ ∀ i ∉ σ, x i = 0} := by
  ext x
  simp only [mem_realization, mem_powerset, supp_subset_iff, Set.mem_ofPred_eq]

theorem convex_realization_powerset (σ : Finset (Fin n)) :
    Convex ℝ (realization σ.powerset) := by
  rw [realization_powerset]
  rintro x ⟨hx0, hx1, hxσ⟩ y ⟨hy0, hy1, hyσ⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_, fun i hi => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx0 i)) (mul_nonneg hb (hy0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx1, hy1, mul_one, mul_one,
      hab]
  · simp [hxσ i hi, hyσ i hi]

theorem vtx_mem_realization_powerset {σ : Finset (Fin n)} {v : Fin n} (hv : v ∈ σ) :
    vtx v ∈ realization σ.powerset :=
  ⟨vtx_nonneg v, sum_vtx v, by rw [supp_vtx, mem_powerset, singleton_subset_iff]; exact hv⟩

/-- The face spanned by `σ` is `conv {eᵢ : i ∈ σ}`, the textbook simplex on `σ`. -/
theorem realization_powerset_eq_convexHull (σ : Finset (Fin n)) :
    realization σ.powerset = convexHull ℝ (vtx '' (σ : Set (Fin n))) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [realization_powerset] at hx
    obtain ⟨hx0, hx1, hxσ⟩ := hx
    have hsum : ∑ i ∈ σ, x i = 1 := by
      rw [← hx1]
      exact Finset.sum_subset (subset_univ σ) (fun i _ hi => hxσ i hi)
    have hmem := σ.centerMass_mem_convexHull (fun i _ => hx0 i) (by rw [hsum]; exact one_pos)
      (z := vtx) (s := vtx '' (σ : Set (Fin n))) (fun i hi => Set.mem_image_of_mem _ hi)
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum] at hmem
    convert hmem using 1
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, vtx, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hj
    · rfl
    · exact hxσ j hj
  · refine convexHull_min ?_ (convex_realization_powerset σ)
    rintro _ ⟨i, hi, rfl⟩
    exact vtx_mem_realization_powerset hi

/-- The full simplex on a nonempty `σ` has contractible realization (it is convex). -/
theorem contractibleSpace_realization_powerset {σ : Finset (Fin n)} (hσ : σ.Nonempty) :
    ContractibleSpace (realization σ.powerset) := by
  obtain ⟨v, hv⟩ := hσ
  exact (convex_realization_powerset σ).contractibleSpace ⟨vtx v, vtx_mem_realization_powerset hv⟩

/-! ### Agreement with the textbook union of simplices -/

/-- For a complex `K` (closed under subsets), `|K|` is the union of the simplices spanned by
its faces, `⋃_{σ ∈ K} |σ|`. -/
theorem realization_eq_iUnion_powerset {K : Finset (Finset (Fin n))} (hK : IsComplex K) :
    realization K = ⋃ σ ∈ K, realization σ.powerset := by
  ext x
  simp only [Set.mem_iUnion, mem_realization, mem_powerset, exists_prop]
  constructor
  · rintro ⟨h0, h1, hx⟩
    exact ⟨supp x, hx, h0, h1, subset_rfl⟩
  · rintro ⟨σ, hσ, h0, h1, hx⟩
    exact ⟨h0, h1, hK σ hσ _ hx⟩

/-- **Textbook form.** For a complex `K`, `|K| = ⋃_{σ ∈ K} conv {eᵢ : i ∈ σ}` (Munkres,
*Elements of Algebraic Topology*; Matoušek, *Using the Borsuk–Ulam Theorem*). -/
theorem realization_eq_iUnion_convexHull {K : Finset (Finset (Fin n))} (hK : IsComplex K) :
    realization K = ⋃ σ ∈ K, convexHull ℝ (vtx '' (σ : Set (Fin n))) := by
  rw [realization_eq_iUnion_powerset hK]
  simp only [realization_powerset_eq_convexHull]

end RimRule
