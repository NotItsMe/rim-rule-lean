import RimRule.Defs

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Theorem 1(b), Case A: the overlap case

Source: council part-2 note §2 ("Case A (overlap)"), with the referee's repair: H1ₘ is applied
at the infimum point `c` itself, which need not lie in `U_j`.

**Setting.** `U₁,…,Uₙ` is an open convex realization of `C` in a stimulus space `X`, and
* `a ∈ U_imp ∖ U_j` (from H5′),
* `b ∈ U_jmp` (from H6),
* `U_i` and `U_j` overlap on the segment `[a, b]` (the Case A assumption).

**Claim.** H1ₘ and F_A cannot both hold.

**Proof (as formalized).** Parametrize `[a, b]` by `f t = lineMap a b t`, `t ∈ [0, 1]`.
1. Let `S = {t > 0 : f t ∈ U_j}`. It is open, bounded below by 0, and nonempty (the overlap
   point `t₀`; note `t₀ ≠ 0` because `a ∉ U_j`). Let `c = inf S`, so `0 ≤ c ≤ t₀`.
2. `f c ∉ U_j`. If `c = 0`, because `a ∉ U_j`. If `c > 0`, then `c ∈ S` would put an interval
   `(l, c]` inside the open set `S`, contradicting `c = inf S`.
3. `f c ∈ U_i` and `f c ∈ U_m ∩ U_p`: the preimages of these convex sets are intervals in `ℝ`
   containing `0, t₀` and `0, 1` respectively, and `c ∈ [0, t₀] ⊆ [0, 1]`.
4. `f c ∈ U_i ⊆ X` (σ_i ≠ ∅), so its codeword is in `C`. It contains i and m but not j, so
   **H1ₘ at `f c`** gives `f c ∈ U_k`. Hence `f c ∈ U_ikmp`.
5. `U_ikmp` is open, so its preimage is an open set containing `c`. Since `c ∈ cl S`, it meets
   `S` at some `t`. The point `f t` lies in `U_ijkmp ⊆ X`, so its codeword contains
   `i ∪ j ∪ k ∪ m ∪ p`, which breaks **F_A**.

Working with the parameter `t ∈ ℝ` replaces "a ball around `c`" in the paper by "an open
interval around `c`"; the two are equivalent because `f` is continuous.
-/

namespace RimRule

open Set

section Helpers

variable {E : Type*} {n : ℕ}

/-- `U_{σ ∪ τ} = U_σ ∩ U_τ`. -/
theorem mem_inter_union {U : Fin n → Set E} {σ τ : Finset (Fin n)} {x : E} :
    x ∈ inter U (σ ∪ τ) ↔ x ∈ inter U σ ∧ x ∈ inter U τ := by
  simp only [mem_inter_iff_subset_codeword, Finset.union_subset_iff]

/-- If `σ ≠ ∅`, then `U_σ ⊆ X` (every `U_s ⊆ X`). This is how we know a codeword is read
at a point of the stimulus space (referee fix 3). -/
theorem mem_X_of_mem_inter {C : Finset (Finset (Fin n))} {X : Set E} {U : Fin n → Set E}
    (hR : IsRealization C X U) {σ : Finset (Fin n)} (hσ : σ.Nonempty) {x : E}
    (hx : x ∈ inter U σ) : x ∈ X := by
  obtain ⟨s, hs⟩ := hσ
  exact hR.subset s (mem_iInter₂.1 hx s hs)

/-- The codeword of a point of `X` is a codeword of `C`. -/
theorem codeword_mem_of_mem_X {C : Finset (Finset (Fin n))} {X : Set E} {U : Fin n → Set E}
    (hR : IsRealization C X U) {x : E} (hx : x ∈ X) : codeword U x ∈ C := by
  have h : codeword U x ∈ (C : Set (Finset (Fin n))) := hR.code_eq ▸ ⟨x, hx, rfl⟩
  exact Finset.mem_coe.1 h

/-- `U_σ` is open when every `U_s` is. -/
theorem isOpen_inter [TopologicalSpace E] {U : Fin n → Set E} (hU : ∀ s, IsOpen (U s))
    (σ : Finset (Fin n)) : IsOpen (inter U σ) :=
  isOpen_biInter_finset fun s _ => hU s

/-- `U_σ` is convex when every `U_s` is. -/
theorem convex_inter [AddCommGroup E] [Module ℝ E] {U : Fin n → Set E}
    (hU : ∀ s, Convex ℝ (U s)) (σ : Finset (Fin n)) : Convex ℝ (inter U σ) :=
  convex_iInter₂ fun s _ => hU s

end Helpers

section CaseA

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **Theorem 1(b), Case A (overlap).** In an open convex realization, take
`a ∈ U_imp ∖ U_j` and `b ∈ U_jmp`. If `U_i` and `U_j` overlap on `[a, b]`, then H1ₘ and F_A
cannot both hold (with `σ_i ≠ ∅`). -/
theorem caseA {n : ℕ} {C : Finset (Finset (Fin n))} {R : Roles n} {X : Set E}
    {U : Fin n → Set E} (hR : IsRealization C X U) (hU : ∀ s, IsOpen (U s) ∧ Convex ℝ (U s))
    (hi : R.i.Nonempty) (h1 : H1m C R) (hFA : FA C R)
    {a b : E} (ha : a ∈ inter U (R.i ∪ R.m ∪ R.p)) (haj : a ∉ inter U R.j)
    (hb : b ∈ inter U (R.j ∪ R.m ∪ R.p))
    (hover : ∃ x ∈ segment ℝ a b, x ∈ inter U R.i ∧ x ∈ inter U R.j) : False := by
  -- The segment `[a, b]`, parametrized by `t ∈ [0, 1]`.
  set f : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a b with hf_def
  have hf : Continuous f := AffineMap.lineMap_continuous
  have hf0 : f 0 = a := AffineMap.lineMap_apply_zero a b
  have hf1 : f 1 = b := AffineMap.lineMap_apply_one a b
  -- Preimages of the sets `U_σ` are open intervals of parameters.
  have hPopen : ∀ σ, IsOpen (f ⁻¹' inter U σ) := fun σ =>
    (isOpen_inter (fun s => (hU s).1) σ).preimage hf
  have hPconv : ∀ σ, Convex ℝ (f ⁻¹' inter U σ) := fun σ =>
    (convex_inter (fun s => (hU s).2) σ).affine_preimage f
  -- Unpack the endpoints.
  rw [mem_inter_union, mem_inter_union] at ha hb
  obtain ⟨⟨hai, ham⟩, hap⟩ := ha
  obtain ⟨⟨-, hbm⟩, hbp⟩ := hb
  have hamp : f 0 ∈ inter U (R.m ∪ R.p) := hf0 ▸ mem_inter_union.2 ⟨ham, hap⟩
  have hbmp : f 1 ∈ inter U (R.m ∪ R.p) := hf1 ▸ mem_inter_union.2 ⟨hbm, hbp⟩
  -- The overlap point `f t₀ ∈ U_i ∩ U_j`.
  obtain ⟨x, hxseg, hxi, hxj⟩ := hover
  rw [segment_eq_image_lineMap] at hxseg
  obtain ⟨t₀, ⟨ht₀0, ht₀1⟩, rfl⟩ := hxseg
  -- Step 1: `S = {t > 0 : f t ∈ U_j}` and `c = inf S`.
  set S : Set ℝ := Ioi 0 ∩ f ⁻¹' inter U R.j with hS_def
  have ht₀pos : 0 < t₀ := by
    rcases ht₀0.eq_or_lt with h | h
    · subst h; exact absurd (hf0 ▸ hxj) haj
    · exact h
  have ht₀S : t₀ ∈ S := ⟨ht₀pos, hxj⟩
  have hSne : S.Nonempty := ⟨t₀, ht₀S⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => le_of_lt ht.1⟩
  set c := sInf S with hc_def
  have hc0 : 0 ≤ c := le_csInf hSne fun t ht => le_of_lt ht.1
  have hct₀ : c ≤ t₀ := csInf_le hSbdd ht₀S
  -- Step 2: `f c ∉ U_j`.
  have hcS : c ∉ S := by
    intro hc
    obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 ((isOpen_Ioi.inter (hPopen R.j)).mem_nhds hc)
    have hmid : (l + c) / 2 ∈ S := hsub ⟨by linarith, by linarith⟩
    have := csInf_le hSbdd hmid
    linarith
  have hcj : f c ∉ inter U R.j := by
    intro h
    rcases hc0.eq_or_lt with h0 | h0
    · rw [← h0, hf0] at h; exact haj h
    · exact hcS ⟨h0, h⟩
  -- Step 3: `f c ∈ U_i` and `f c ∈ U_mp`.
  have h0i : (0 : ℝ) ∈ f ⁻¹' inter U R.i := by rw [mem_preimage, hf0]; exact hai
  have hci : f c ∈ inter U R.i := (hPconv R.i).ordConnected.out h0i hxi ⟨hc0, hct₀⟩
  have hcmp : f c ∈ inter U (R.m ∪ R.p) :=
    (hPconv _).ordConnected.out hamp hbmp ⟨hc0, hct₀.trans ht₀1⟩
  -- Step 4: H1ₘ at `f c` gives `f c ∈ U_k`.
  have hcC : codeword U (f c) ∈ C := codeword_mem_of_mem_X hR (mem_X_of_mem_inter hR hi hci)
  have hck : f c ∈ inter U R.k := by
    rw [mem_inter_iff_subset_codeword] at hci hcj hcmp ⊢
    rw [Finset.union_subset_iff] at hcmp
    exact h1 _ hcC (Finset.union_subset hci hcmp.1) hcj
  have hcW : f c ∈ inter U (R.i ∪ R.k ∪ R.m ∪ R.p) := by
    rw [mem_inter_union] at hcmp
    exact mem_inter_union.2 ⟨mem_inter_union.2 ⟨mem_inter_union.2 ⟨hci, hck⟩, hcmp.1⟩, hcmp.2⟩
  -- Step 5: an open interval around `c` meets `S`, giving a point of `U_ijkmp`.
  obtain ⟨t, htW, -, htj⟩ :=
    mem_closure_iff.1 (csInf_mem_closure hSne hSbdd) _ (hPopen _) hcW
  have hti : f t ∈ inter U R.i := by
    simp only [mem_preimage, mem_inter_union] at htW
    exact htW.1.1.1
  have htC : codeword U (f t) ∈ C := codeword_mem_of_mem_X hR (mem_X_of_mem_inter hR hi hti)
  apply hFA _ htC
  simp only [mem_preimage, mem_inter_iff_subset_codeword, Finset.union_subset_iff] at htW htj ⊢
  exact ⟨⟨⟨⟨htW.1.1.1, htj⟩, htW.1.1.2⟩, htW.1.2⟩, htW.2⟩

/-- Case A on `ℝ^d = Fin d → ℝ`, the space used in `IsOpenConvex`. -/
theorem caseA_realSpace {d n : ℕ} {C : Finset (Finset (Fin n))} {R : Roles n}
    {X : Set (RealSpace d)} {U : Fin n → Set (RealSpace d)} (hR : IsRealization C X U)
    (hU : ∀ s, IsOpen (U s) ∧ Convex ℝ (U s)) (hi : R.i.Nonempty) (h1 : H1m C R)
    (hFA : FA C R) {a b : RealSpace d} (ha : a ∈ inter U (R.i ∪ R.m ∪ R.p))
    (haj : a ∉ inter U R.j) (hb : b ∈ inter U (R.j ∪ R.m ∪ R.p))
    (hover : ∃ x ∈ segment ℝ a b, x ∈ inter U R.i ∧ x ∈ inter U R.j) : False :=
  caseA hR hU hi h1 hFA ha haj hb hover

end CaseA

end RimRule
