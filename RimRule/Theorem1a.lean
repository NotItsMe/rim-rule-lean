import RimRule.CaseB
import RimRule.Census

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Theorem 1(a) (closed Rim)

`theorem1a` proves `Theorem1a` exactly as stated in `RimRule/Defs.lean`.

Source: council part-2 note §1 ("Closed Rim: statement and full proof") and §5, with the
referee fixes (fix 4: in closed Case B, `h(r) > 0`; fix 3: where codewords are read).

**Setting.** `V₁,…,Vₙ` is a closed convex realization of `C` in a stimulus space `X`, and
* `a ∈ V_imp ∖ V_j` (H5′), `b ∈ V_jmp` (H6), `z ∈ V_ijm` (H7).

**Case A (`caseA_closed`): `V_i` and `V_j` overlap on `[a, b]`.** Parametrize `[a, b]` by
`f t = lineMap a b t`. Let `S = {t ≥ 0 : f t ∈ V_j}` and `c = inf S`.
1. `S` is closed, so `c ∈ S`: `f c ∈ V_j`. Since `a ∉ V_j`, `c > 0`.
2. For `t ∈ [0, c)`: `f t ∈ V_i ∩ V_m` (convexity) and `f t ∉ V_j` (`t < inf S`), so
   **H1ₘ** gives `f t ∈ V_k`. `V_k` is closed and `c ∈ cl [0, c)`, so `f c ∈ V_k`.
3. Also `f c ∈ V_i ∩ V_m ∩ V_p` (convexity). So `c(f c)` contains `ijkmp`: breaks **F_A**.

**Case B (`caseB_closed`): `[a, b]` misses `W = V_i ∩ V_j`.** `W` is closed, so the lowest
point `r` of `W` in the triangle exists (`exists_lowest`, as in the open Case B: minimise the
z-weight over representations, so no non-degeneracy step is needed).
1. `[a, r) ⊆ V_i` by plain convexity (Rockafellar 6.1 is not needed, and a closed `V_i` may
   have empty interior). Its points are lower than `r` or on `[a, b]`, so they miss `W`;
   **H1ₘ** puts them in `V_k`. Closedness gives `r ∈ V_k`.
2. Mirror on `[b, r)` with **H2ₘ**: `r ∈ V_l`.
3. `r ∈ W` and `r ∈ V_m` (convexity). So `c(r)` contains `ijklm`: breaks **F_B**.

`σ_m = ∅` is allowed throughout; no step uses `σ_m ≠ ∅`.

`C033_not_isClosedConvex` is the corollary: C5-033 is not closed-convex, because the census
(`Census.theorem1a_hyps`) checks every hypothesis of Theorem 1(a) on it.
-/

namespace RimRule

open Set

/-- `V_σ` is closed when every `V_s` is. -/
theorem isClosed_interU {E : Type*} [TopologicalSpace E] {n : ℕ} {U : Fin n → Set E}
    (hU : ∀ s, IsClosed (U s)) (σ : Finset (Fin n)) : IsClosed (inter U σ) :=
  isClosed_biInter fun s _ => hU s

section Closed

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **Theorem 1(a), Case A (overlap).** In a closed convex realization, take
`a ∈ V_imp ∖ V_j` and `b ∈ V_jmp`. If `V_i` and `V_j` overlap on `[a, b]`, then H1ₘ and F_A
cannot both hold (with `σ_i ≠ ∅`). -/
theorem caseA_closed {n : ℕ} {C : Finset (Finset (Fin n))} {R : Roles n} {X : Set E}
    {U : Fin n → Set E} (hR : IsRealization C X U) (hU : ∀ s, IsClosed (U s) ∧ Convex ℝ (U s))
    (hi : R.i.Nonempty) (h1 : H1m C R) (hFA : FA C R)
    {a b : E} (ha : a ∈ inter U (R.i ∪ R.m ∪ R.p)) (haj : a ∉ inter U R.j)
    (hb : b ∈ inter U (R.j ∪ R.m ∪ R.p))
    (hover : ∃ x ∈ segment ℝ a b, x ∈ inter U R.i ∧ x ∈ inter U R.j) : False := by
  -- The segment `[a, b]`, parametrized by `t ∈ [0, 1]`.
  set f : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a b with hf_def
  have hf : Continuous f := AffineMap.lineMap_continuous
  have hf0 : f 0 = a := AffineMap.lineMap_apply_zero a b
  have hf1 : f 1 = b := AffineMap.lineMap_apply_one a b
  -- Preimages of the sets `V_σ` are closed intervals of parameters.
  have hPclosed : ∀ σ, IsClosed (f ⁻¹' inter U σ) := fun σ =>
    (isClosed_interU (fun s => (hU s).1) σ).preimage hf
  have hPconv : ∀ σ, Convex ℝ (f ⁻¹' inter U σ) := fun σ =>
    (convex_inter (fun s => (hU s).2) σ).affine_preimage f
  -- Unpack the endpoints.
  rw [mem_inter_union, mem_inter_union] at ha hb
  obtain ⟨⟨hai, ham⟩, hap⟩ := ha
  obtain ⟨⟨-, hbm⟩, hbp⟩ := hb
  have hamp : f 0 ∈ inter U (R.m ∪ R.p) := hf0 ▸ mem_inter_union.2 ⟨ham, hap⟩
  have hbmp : f 1 ∈ inter U (R.m ∪ R.p) := hf1 ▸ mem_inter_union.2 ⟨hbm, hbp⟩
  have h0i : (0 : ℝ) ∈ f ⁻¹' inter U R.i := by rw [mem_preimage, hf0]; exact hai
  -- The overlap point `f t₀ ∈ V_i ∩ V_j`.
  obtain ⟨x, hxseg, hxi, hxj⟩ := hover
  rw [segment_eq_image_lineMap] at hxseg
  obtain ⟨t₀, ⟨ht₀0, ht₀1⟩, rfl⟩ := hxseg
  -- Step 1: `S = {t ≥ 0 : f t ∈ V_j}` is closed, so `c = inf S ∈ S`, and `c > 0`.
  set S : Set ℝ := Ici 0 ∩ f ⁻¹' inter U R.j with hS_def
  have ht₀S : t₀ ∈ S := ⟨ht₀0, hxj⟩
  have hSne : S.Nonempty := ⟨t₀, ht₀S⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  set c := sInf S with hc_def
  have hcS : c ∈ S := (isClosed_Ici.inter (hPclosed R.j)).csInf_mem hSne hSbdd
  have hct₀ : c ≤ t₀ := csInf_le hSbdd ht₀S
  have hcj : f c ∈ inter U R.j := hcS.2
  have hc0 : 0 < c := by
    have h0c : (0 : ℝ) ≤ c := hcS.1
    rcases h0c.eq_or_lt with h | h
    · exfalso
      have hc := hcj
      rw [← h, hf0] at hc
      exact haj hc
    · exact h
  -- Step 2: `f '' [0, c) ⊆ V_k` by H1ₘ, and `V_k` is closed, so `f c ∈ V_k`.
  have hIco : Ico 0 c ⊆ f ⁻¹' inter U R.k := by
    rintro t ⟨ht0, htc⟩
    have hti : f t ∈ inter U R.i :=
      (hPconv R.i).ordConnected.out h0i hxi ⟨ht0, htc.le.trans hct₀⟩
    have htmp : f t ∈ inter U (R.m ∪ R.p) :=
      (hPconv _).ordConnected.out hamp hbmp ⟨ht0, (htc.le.trans hct₀).trans ht₀1⟩
    have htj : f t ∉ inter U R.j := fun h => (not_le.2 htc) (csInf_le hSbdd ⟨ht0, h⟩)
    have htC := codeword_mem_of_mem_X hR (mem_X_of_mem_inter hR hi hti)
    change f t ∈ inter U R.k
    rw [mem_inter_iff_subset_codeword] at hti htj htmp ⊢
    rw [Finset.union_subset_iff] at htmp
    exact h1 _ htC (Finset.union_subset hti htmp.1) htj
  have hck : f c ∈ inter U R.k := by
    have hcl : c ∈ closure (Ico 0 c) := by
      rw [closure_Ico hc0.ne]
      exact right_mem_Icc.2 hc0.le
    exact closure_minimal hIco (hPclosed R.k) hcl
  -- Step 3: `f c ∈ V_ijkmp`, which breaks F_A.
  have hci : f c ∈ inter U R.i := (hPconv R.i).ordConnected.out h0i hxi ⟨hc0.le, hct₀⟩
  have hcmp : f c ∈ inter U (R.m ∪ R.p) :=
    (hPconv _).ordConnected.out hamp hbmp ⟨hc0.le, hct₀.trans ht₀1⟩
  have hcC := codeword_mem_of_mem_X hR (mem_X_of_mem_inter hR hi hci)
  apply hFA _ hcC
  rw [mem_inter_iff_subset_codeword] at hci hcj hck hcmp
  rw [Finset.union_subset_iff] at hcmp
  exact Finset.union_subset (Finset.union_subset
    (Finset.union_subset (Finset.union_subset hci hcj) hck) hcmp.1) hcmp.2

/-- **Theorem 1(a), Case B (no overlap).** In a closed convex realization, take
`a ∈ V_imp ∖ V_j`, `b ∈ V_jmp` and `z ∈ V_ijm`. If `[a, b]` misses `V_i ∩ V_j`, then H1ₘ,
H2ₘ and F_B cannot all hold (with `σ_i ≠ ∅`). -/
theorem caseB_closed {n : ℕ} {C : Finset (Finset (Fin n))} {R : Roles n} {X : Set E}
    {U : Fin n → Set E} (hR : IsRealization C X U) (hU : ∀ s, IsClosed (U s) ∧ Convex ℝ (U s))
    (hi : R.i.Nonempty) (h1 : H1m C R) (h2 : H2m C R) (hFB : FB C R)
    {a b z : E} (ha : a ∈ inter U (R.i ∪ R.m ∪ R.p)) (haj : a ∉ inter U R.j)
    (hb : b ∈ inter U (R.j ∪ R.m ∪ R.p)) (hz : z ∈ inter U (R.i ∪ R.j ∪ R.m))
    (hno : ¬ ∃ x ∈ segment ℝ a b, x ∈ inter U R.i ∧ x ∈ inter U R.j) : False := by
  have hUk : ∀ σ, IsClosed (inter U σ) := isClosed_interU fun s => (hU s).1
  have hUc : ∀ σ, Convex ℝ (inter U σ) := convex_inter fun s => (hU s).2
  -- Unpack the three points.
  rw [mem_inter_union, mem_inter_union] at ha hb hz
  obtain ⟨⟨hai, ham⟩, -⟩ := ha
  obtain ⟨⟨hbj, hbm⟩, -⟩ := hb
  obtain ⟨⟨hzi, hzj⟩, hzm⟩ := hz
  -- `σ_j ≠ ∅`, since `a ∉ V_j`.
  have hj : R.j.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro h
    exact haj (by simp [h, inter])
  -- The lowest point `r = tri a b z w` of the closed set `W = V_i ∩ V_j` in the triangle.
  obtain ⟨w, hw, hwF, hwmin⟩ := exists_lowest (F := inter U R.i ∩ inter U R.j)
    ((hUk R.i).inter (hUk R.j)) a b z
    ⟨(0, 0, 1), ⟨le_rfl, le_rfl, zero_le_one, by norm_num⟩,
      by simpa [tri] using (⟨hzi, hzj⟩ : z ∈ inter U R.i ∩ inter U R.j)⟩
  obtain ⟨hw1, hw2, hw3, hwsum⟩ := hw
  set r := tri a b z w with hr_def
  have hri : r ∈ inter U R.i := hwF.1
  have hrj : r ∈ inter U R.j := hwF.2
  have hrm : r ∈ inter U R.m := tri_mem_of_convex (hUc R.m) ham hbm hzm ⟨hw1, hw2, hw3, hwsum⟩
  -- Key fact: a representation that is lower than `w`, or on the base, is not in `W`.
  have key : ∀ q ∈ simplex3, (q.2.2 < w.2.2 ∨ q.2.2 = 0) →
      tri a b z q ∉ inter U R.i ∩ inter U R.j := by
    rintro q ⟨hq1, hq2, hq3, hqsum⟩ hcase hW
    rcases hcase with hlt | h0
    · have := hwmin q ⟨hq1, hq2, hq3, hqsum⟩ hW
      linarith
    · refine hno ⟨tri a b z q, ⟨q.1, q.2.1, hq1, hq2, by linarith, ?_⟩, hW⟩
      simp [tri, h0]
  -- The z-weight of a point of an open segment `(p, r)` is lower than `w`, or zero.
  have lower : ∀ s t : ℝ, 0 < s → 0 < t → s + t = 1 → (t * w.2.2 < w.2.2 ∨ t * w.2.2 = 0) := by
    intro s t hs ht hst
    rcases hw3.eq_or_lt with h | h
    · right; rw [← h, mul_zero]
    · left; exact mul_lt_of_lt_one_left h (by linarith)
  -- Step 1: `(a, r) ⊆ V_k`, by H1ₘ (plain convexity puts `(a, r)` in `V_i ∩ V_m`).
  have hsegk : openSegment ℝ a r ⊆ inter U R.k := by
    intro y hy
    have hyi := (hUc R.i).openSegment_subset hai hri hy
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
  -- Step 2: `(b, r) ⊆ V_l`, by H2ₘ.
  have hsegl : openSegment ℝ b r ⊆ inter U R.l := by
    intro y hy
    have hyj := (hUc R.j).openSegment_subset hbj hrj hy
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
  -- `V_k` and `V_l` are closed, so they contain the endpoint `r`.
  have hrk : r ∈ inter U R.k := closure_minimal hsegk (hUk R.k)
    (segment_subset_closure_openSegment (right_mem_segment ℝ a r))
  have hrl : r ∈ inter U R.l := closure_minimal hsegl (hUk R.l)
    (segment_subset_closure_openSegment (right_mem_segment ℝ b r))
  -- Step 3: `r ∈ V_ijklm`, which breaks F_B.
  have hC := codeword_mem_of_mem_X hR (mem_X_of_mem_inter hR hi hri)
  apply hFB _ hC
  rw [mem_inter_iff_subset_codeword] at hri hrj hrk hrl hrm
  exact Finset.union_subset (Finset.union_subset
    (Finset.union_subset (Finset.union_subset hri hrj) hrk) hrl) hrm

end Closed

/-- **Theorem 1(a) (closed Rim).** Let `σ_i ≠ ∅`. If `C` satisfies the core hypotheses
(H1ₘ, H2ₘ, H5′, H6, H7, F_A) together with F_B, then `C` is not closed-convex. -/
theorem theorem1a : Theorem1a := by
  intro n C R hi hcore hFB hclosed
  obtain ⟨d, X, U, hR, hU⟩ := hclosed
  -- `a` from H5′: a codeword containing i, m, p and not j.
  obtain ⟨ca, hca, hca_sub, hca_j⟩ := hcore.h5'
  obtain ⟨a, -, rfl⟩ := exists_point_of_mem_code hR hca
  -- `b` from H6: a codeword containing j, m, p.
  obtain ⟨cb, hcb, hcb_sub⟩ := hcore.h6
  obtain ⟨b, -, rfl⟩ := exists_point_of_mem_code hR hcb
  -- `z` from H7: a codeword containing i, j, m.
  obtain ⟨cz, hcz, hcz_sub⟩ := hcore.h7
  obtain ⟨z, -, rfl⟩ := exists_point_of_mem_code hR hcz
  have ha : a ∈ inter U (R.i ∪ R.m ∪ R.p) := (mem_inter_iff_subset_codeword U _ a).2 hca_sub
  have haj : a ∉ inter U R.j := fun h => hca_j ((mem_inter_iff_subset_codeword U _ a).1 h)
  have hb : b ∈ inter U (R.j ∪ R.m ∪ R.p) := (mem_inter_iff_subset_codeword U _ b).2 hcb_sub
  have hz : z ∈ inter U (R.i ∪ R.j ∪ R.m) := (mem_inter_iff_subset_codeword U _ z).2 hcz_sub
  -- Case A (overlap on `[a, b]`) or Case B (no overlap).
  by_cases hover : ∃ x ∈ segment ℝ a b, x ∈ inter U R.i ∧ x ∈ inter U R.j
  · exact caseA_closed hR hU hi hcore.h1m hcore.fA ha haj hb hover
  · exact caseB_closed hR hU hi hcore.h1m hcore.h2m hFB ha haj hb hz hover

/-- **Corollary.** C5-033 is not closed-convex: Theorem 1(a) applies with roles
`(i,j,k,l,m,p) = (4,5,1,2,3,6)`, and the census checks every hypothesis. -/
theorem C033_not_isClosedConvex : ¬ IsClosedConvex Census.C033 := by
  obtain ⟨hi, hcore, hFB⟩ := Census.theorem1a_hyps
  exact theorem1a 7 Census.C033 Census.R033 hi hcore hFB

end RimRule
