import RimRule.CaseA
import RimRule.Rockafellar

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Theorem 1(b), Case B: the lowest-point case

Source: council part-2 note §2 ("Case B (no overlap)"), with referee fixes 2–4
(the cases `r = a`, `r = b`, `h(r) = 0`, and where codewords are read).

**Setting.** `U₁,…,Uₙ` is an open convex realization of `C` in a stimulus space `X`, and
* `a ∈ U_imp ∖ U_j` (H5′), `b ∈ U_jmp` (H6), `z ∈ U_ijm` (H7),
* `[a, b]` misses `W = U_i ∩ U_j` (the Case B assumption, the negation of Case A's).

**Claim.** H1ₘ, H2ₘ, H3 and H4 cannot all hold (with `σ_i ≠ ∅`).

## How "the lowest point" is formalized

The paper takes the affine height `h` on the triangle `T = conv(a, b, z)` (`h = 0` on `[a, b]`,
`h(z) = 1`) and lets `r` minimise `h` on `cl W ∩ T`. That needs `T` to be non-degenerate.

Here we minimise the **weight of `z`** instead, over *representations*: let
`K = {(α, β, γ) ∈ Δ : αa + βb + γz ∈ cl W}`, where `Δ` is the standard 2-simplex. `K` is
compact (closed in `Δ`) and nonempty (`(0, 0, 1) ↦ z ∈ W`), so some `w = (α, β, γ) ∈ K` has
least `γ`. Put `r = αa + βb + γz`. When `T` is a genuine triangle, `γ = h`, so this is the
paper's `r`. But the argument below never needs non-degeneracy, so B1 of the paper
("the triangle is non-degenerate") is not needed.

**Key fact.** If `q ∈ Δ` and either `q_γ < γ` or `q_γ = 0`, then `q_a a + q_b b + q_γ z ∉ W`.
* If `q_γ < γ`: a point of `W` with that representation would put `q` in `K`, below the minimum.
* If `q_γ = 0`: the point lies on `[a, b]`, which misses `W`.

**Proof.**
1. `r ∈ cl W ⊆ cl U_i ∩ cl U_j`, and `r ∈ T ⊆ U_m` (convexity).
2. A point `y = s a + t r` of the open segment `(a, r)` (`s, t > 0`, `s + t = 1`) has the
   representation `(s + tα, tβ, tγ)`. Its z-weight `tγ` is `< γ` if `γ > 0`, and `= 0` if `γ = 0`.
   So `y ∉ W` by the key fact. This covers `h(r) = 0` without a separate case.
3. Rockafellar 6.1 puts `(a, r)` in `U_i`, and convexity puts it in `U_m`. So `y ∈ U_i ∩ U_m`,
   `y ∉ U_j`, and `y ∈ X` (σ_i ≠ ∅). **H1ₘ** gives `y ∈ U_k`. So `(a, r) ⊆ U_k` and
   `r ∈ cl U_k`. If `r = a`, then `(a, a) = {a}` in mathlib, so the same argument is H1ₘ
   applied at `a` (the referee's fix for `r = a`); no separate case is needed.
4. Mirror: `(b, r) ⊆ U_l` via **H2ₘ** (points lie in `U_j ⊆ X`, since `a ∉ U_j` forces
   `σ_j ≠ ∅`). So `r ∈ cl U_l`. If `r = b`, this is H2ₘ at `b`, where `b ∉ U_i` comes from the
   key fact (`b` has z-weight 0).
5. **H3** gives a point of `U_k ∩ U_l`, so Rockafellar 6.5 (Stage 3) gives
   `r ∈ cl U_k ∩ cl U_l ⊆ cl (U_k ∩ U_l)`.
6. `U_m` is open and contains `r`, so it meets `U_k ∩ U_l` at some `y`. `σ_m ≠ ∅` (H3 + H4), so
   `y ∈ X`, and its codeword contains `k ∪ l ∪ m`, which breaks **H4**.
-/

namespace RimRule

open Set

/-! ### The standard 2-simplex and the triangle map -/

/-- The standard 2-simplex `Δ = {(α, β, γ) : α, β, γ ≥ 0, α + β + γ = 1}`. -/
def simplex3 : Set (ℝ × ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2 ∧ q.1 + q.2.1 + q.2.2 = 1}

theorem isCompact_simplex3 : IsCompact simplex3 := by
  have hbox : IsCompact (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  refine hbox.of_isClosed_subset ?_ ?_
  · have h1 : Continuous fun q : ℝ × ℝ × ℝ => q.1 := continuous_fst
    have h2 : Continuous fun q : ℝ × ℝ × ℝ => q.2.1 := continuous_fst.comp continuous_snd
    have h3 : Continuous fun q : ℝ × ℝ × ℝ => q.2.2 := continuous_snd.comp continuous_snd
    simp only [simplex3, ofPred_and]
    exact (isClosed_le continuous_const h1).inter ((isClosed_le continuous_const h2).inter
      ((isClosed_le continuous_const h3).inter (isClosed_eq ((h1.add h2).add h3)
        continuous_const)))
  · rintro ⟨α, β, γ⟩ ⟨hα, hβ, hγ, hs⟩
    exact ⟨⟨hα, by linarith⟩, ⟨hβ, by linarith⟩, ⟨hγ, by linarith⟩⟩

section Triangle

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The point `αa + βb + γz` of the triangle `conv(a, b, z)` with weights `q = (α, β, γ)`. -/
def tri (a b z : E) (q : ℝ × ℝ × ℝ) : E :=
  q.1 • a + q.2.1 • b + q.2.2 • z

/-- A convex set containing `a, b, z` contains every point of the triangle. -/
theorem tri_mem_of_convex {s : Set E} (hs : Convex ℝ s) {a b z : E} (ha : a ∈ s) (hb : b ∈ s)
    (hz : z ∈ s) {q : ℝ × ℝ × ℝ} (hq : q ∈ simplex3) : tri a b z q ∈ s := by
  obtain ⟨hα, hβ, hγ, hsum⟩ := hq
  have h := hs.sum_mem (t := Finset.univ) (w := ![q.1, q.2.1, q.2.2]) (z := ![a, b, z])
    (by intro i _; fin_cases i <;> simpa)
    (by simpa [Fin.sum_univ_three] using hsum)
    (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_three, tri] using h

/-- Weights of the point `s • p + t • r` when `r = tri a b z w`, for `p = a`. -/
theorem tri_combo_left (a b z : E) (w : ℝ × ℝ × ℝ) (s t : ℝ) :
    s • a + t • tri a b z w = tri a b z (s + t * w.1, t * w.2.1, t * w.2.2) := by
  simp only [tri, smul_add, smul_smul, add_smul]
  abel

/-- Weights of the point `s • p + t • r` when `r = tri a b z w`, for `p = b`. -/
theorem tri_combo_right (a b z : E) (w : ℝ × ℝ × ℝ) (s t : ℝ) :
    s • b + t • tri a b z w = tri a b z (t * w.1, s + t * w.2.1, t * w.2.2) := by
  simp only [tri, smul_add, smul_smul, add_smul]
  abel

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem continuous_tri (a b z : E) : Continuous (tri a b z) := by
  unfold tri
  fun_prop

/-- **The lowest point.** If a closed set `F` meets the triangle, some representation
`w ∈ Δ` with `tri w ∈ F` has the least z-weight among all such representations. -/
theorem exists_lowest {F : Set E} (hF : IsClosed F) (a b z : E)
    (hne : ∃ q ∈ simplex3, tri a b z q ∈ F) :
    ∃ w ∈ simplex3, tri a b z w ∈ F ∧
      ∀ q ∈ simplex3, tri a b z q ∈ F → w.2.2 ≤ q.2.2 := by
  have hK : IsCompact (simplex3 ∩ tri a b z ⁻¹' F) :=
    isCompact_simplex3.inter_right (hF.preimage (continuous_tri a b z))
  obtain ⟨q₀, hq₀, hq₀F⟩ := hne
  obtain ⟨w, ⟨hw, hwF⟩, hmin⟩ := hK.exists_isMinOn ⟨q₀, hq₀, hq₀F⟩
    (continuous_snd.comp continuous_snd).continuousOn
  exact ⟨w, hw, hwF, fun q hq hqF => isMinOn_iff.1 hmin q ⟨hq, hqF⟩⟩

end Triangle

/-! ### Case B -/

/-- A codeword of `C` is the codeword of some point of `X`. -/
theorem exists_point_of_mem_code {E : Type*} {n : ℕ} {C : Finset (Finset (Fin n))} {X : Set E}
    {U : Fin n → Set E} (hR : IsRealization C X U) {c : Finset (Fin n)} (hc : c ∈ C) :
    ∃ x ∈ X, codeword U x = c := by
  have h : c ∈ codeOf X U := hR.code_eq ▸ Finset.mem_coe.2 hc
  exact h

section CaseB

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **Theorem 1(b), Case B (no overlap).** In an open convex realization, take
`a ∈ U_imp ∖ U_j`, `b ∈ U_jmp` and `z ∈ U_ijm`. If `[a, b]` misses `U_i ∩ U_j`, then H1ₘ, H2ₘ,
H3 and H4 cannot all hold (with `σ_i ≠ ∅`). -/
theorem caseB {n : ℕ} {C : Finset (Finset (Fin n))} {R : Roles n} {X : Set E}
    {U : Fin n → Set E} (hR : IsRealization C X U) (hU : ∀ s, IsOpen (U s) ∧ Convex ℝ (U s))
    (hi : R.i.Nonempty) (h1 : H1m C R) (h2 : H2m C R) (h3 : H3 C R) (h4 : H4 C R)
    {a b z : E} (ha : a ∈ inter U (R.i ∪ R.m ∪ R.p)) (haj : a ∉ inter U R.j)
    (hb : b ∈ inter U (R.j ∪ R.m ∪ R.p)) (hz : z ∈ inter U (R.i ∪ R.j ∪ R.m))
    (hno : ¬ ∃ x ∈ segment ℝ a b, x ∈ inter U R.i ∧ x ∈ inter U R.j) : False := by
  have hUo : ∀ σ, IsOpen (inter U σ) := isOpen_inter fun s => (hU s).1
  have hUc : ∀ σ, Convex ℝ (inter U σ) := convex_inter fun s => (hU s).2
  -- Unpack the three points.
  rw [mem_inter_union, mem_inter_union] at ha hb hz
  obtain ⟨⟨hai, ham⟩, -⟩ := ha
  obtain ⟨⟨hbj, hbm⟩, -⟩ := hb
  obtain ⟨⟨hzi, hzj⟩, hzm⟩ := hz
  -- `σ_j ≠ ∅` (since `a ∉ U_j`) and `σ_m ≠ ∅` (H3 + H4).
  have hj : R.j.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro h
    exact haj (by simp [h, inter])
  have hm : R.m.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro h
    obtain ⟨c, hc, hkl⟩ := h3
    exact h4 c hc (by simpa [h] using hkl)
  -- The lowest point `r = tri a b z w` of `cl W` in the triangle, `W = U_i ∩ U_j`.
  obtain ⟨w, hw, hwF, hwmin⟩ := exists_lowest (F := closure (inter U R.i ∩ inter U R.j))
    isClosed_closure a b z
    ⟨(0, 0, 1), ⟨le_rfl, le_rfl, zero_le_one, by norm_num⟩,
      subset_closure (by simpa [tri] using (⟨hzi, hzj⟩ : z ∈ inter U R.i ∩ inter U R.j))⟩
  obtain ⟨hw1, hw2, hw3, hwsum⟩ := hw
  set r := tri a b z w with hr_def
  have hri : r ∈ closure (inter U R.i) := closure_mono inter_subset_left hwF
  have hrj : r ∈ closure (inter U R.j) := closure_mono inter_subset_right hwF
  have hrm : r ∈ inter U R.m := tri_mem_of_convex (hUc R.m) ham hbm hzm ⟨hw1, hw2, hw3, hwsum⟩
  -- Key fact: a representation that is lower than `w`, or on the base, is not in `W`.
  have key : ∀ q ∈ simplex3, (q.2.2 < w.2.2 ∨ q.2.2 = 0) →
      tri a b z q ∉ inter U R.i ∩ inter U R.j := by
    rintro q ⟨hq1, hq2, hq3, hqsum⟩ hcase hW
    rcases hcase with hlt | h0
    · have := hwmin q ⟨hq1, hq2, hq3, hqsum⟩ (subset_closure hW)
      linarith
    · refine hno ⟨tri a b z q, ⟨q.1, q.2.1, hq1, hq2, by linarith, ?_⟩, hW⟩
      simp [tri, h0]
  -- The z-weight of a point of an open segment `(p, r)` is lower than `w`, or zero.
  have lower : ∀ s t : ℝ, 0 < s → 0 < t → s + t = 1 → (t * w.2.2 < w.2.2 ∨ t * w.2.2 = 0) := by
    intro s t hs ht hst
    rcases hw3.eq_or_lt with h | h
    · right; rw [← h, mul_zero]
    · left; exact mul_lt_of_lt_one_left h (by linarith)
  -- Step 3: `(a, r) ⊆ U_k`, by H1ₘ.
  have hsegk : openSegment ℝ a r ⊆ inter U R.k := by
    intro y hy
    have hyi := openSegment_subset_of_isOpen_convex (hUo R.i) (hUc R.i) hai hri hy
    have hym := (hUc R.m).openSegment_subset ham hrm hy
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hy
    have hyj : s • a + t • r ∉ inter U R.j := by
      intro hyj
      rw [hr_def, tri_combo_left] at hyi hyj
      refine key _ ⟨by positivity, by positivity, by positivity, ?_⟩ (lower s t hs ht hst)
        ⟨hyi, hyj⟩
      linear_combination hst + t * hwsum
    have hC := codeword_mem_of_mem_X hR (mem_X_of_mem_inter hR hi hyi)
    rw [mem_inter_iff_subset_codeword] at hyi hym hyj ⊢
    exact h1 _ hC (Finset.union_subset hyi hym) hyj
  -- Step 4: `(b, r) ⊆ U_l`, by H2ₘ.
  have hsegl : openSegment ℝ b r ⊆ inter U R.l := by
    intro y hy
    have hyj := openSegment_subset_of_isOpen_convex (hUo R.j) (hUc R.j) hbj hrj hy
    have hym := (hUc R.m).openSegment_subset hbm hrm hy
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hy
    have hyi : s • b + t • r ∉ inter U R.i := by
      intro hyi
      rw [hr_def, tri_combo_right] at hyi hyj
      refine key _ ⟨by positivity, by positivity, by positivity, ?_⟩ (lower s t hs ht hst)
        ⟨hyi, hyj⟩
      linear_combination hst + t * hwsum
    have hC := codeword_mem_of_mem_X hR (mem_X_of_mem_inter hR hj hyj)
    rw [mem_inter_iff_subset_codeword] at hyi hym hyj ⊢
    exact h2 _ hC (Finset.union_subset hyj hym) hyi
  have hrk : r ∈ closure (inter U R.k) :=
    closure_mono hsegk (segment_subset_closure_openSegment (right_mem_segment ℝ a r))
  have hrl : r ∈ closure (inter U R.l) :=
    closure_mono hsegl (segment_subset_closure_openSegment (right_mem_segment ℝ b r))
  -- Step 5: H3 gives a point of `U_k ∩ U_l`, so Rockafellar 6.5 applies.
  have hkl : (inter U R.k ∩ inter U R.l).Nonempty := by
    obtain ⟨c, hc, hklc⟩ := h3
    obtain ⟨x, -, rfl⟩ := exists_point_of_mem_code hR hc
    rw [Finset.union_subset_iff] at hklc
    exact ⟨x, (mem_inter_iff_subset_codeword U R.k x).2 hklc.1,
      (mem_inter_iff_subset_codeword U R.l x).2 hklc.2⟩
  have hrkl : r ∈ closure (inter U R.k ∩ inter U R.l) :=
    closure_inter_closure_subset_closure_inter (hUo R.k) (hUc R.k) (hUo R.l) (hUc R.l) hkl
      ⟨hrk, hrl⟩
  -- Step 6: `U_m` is open around `r`, so it meets `U_k ∩ U_l`; that breaks H4.
  obtain ⟨y, hym, hyk, hyl⟩ := mem_closure_iff.1 hrkl _ (hUo R.m) hrm
  have hC := codeword_mem_of_mem_X hR (mem_X_of_mem_inter hR hm hym)
  apply h4 _ hC
  rw [mem_inter_iff_subset_codeword] at hym hyk hyl
  exact Finset.union_subset (Finset.union_subset hyk hyl) hym

/-- Case B on `ℝ^d = Fin d → ℝ`, the space used in `IsOpenConvex`. -/
theorem caseB_realSpace {d n : ℕ} {C : Finset (Finset (Fin n))} {R : Roles n}
    {X : Set (RealSpace d)} {U : Fin n → Set (RealSpace d)} (hR : IsRealization C X U)
    (hU : ∀ s, IsOpen (U s) ∧ Convex ℝ (U s)) (hi : R.i.Nonempty) (h1 : H1m C R)
    (h2 : H2m C R) (h3 : H3 C R) (h4 : H4 C R) {a b z : RealSpace d}
    (ha : a ∈ inter U (R.i ∪ R.m ∪ R.p)) (haj : a ∉ inter U R.j)
    (hb : b ∈ inter U (R.j ∪ R.m ∪ R.p)) (hz : z ∈ inter U (R.i ∪ R.j ∪ R.m))
    (hno : ¬ ∃ x ∈ segment ℝ a b, x ∈ inter U R.i ∧ x ∈ inter U R.j) : False :=
  caseB hR hU hi h1 h2 h3 h4 ha haj hb hz hno

end CaseB

end RimRule
