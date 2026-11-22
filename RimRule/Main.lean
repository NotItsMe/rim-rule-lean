import RimRule.CaseB
import RimRule.Census

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Theorem 1(b) (Rim\*), assembled

`theorem1b` proves `Theorem1b` exactly as stated in `RimRule/Defs.lean`.

Proof (council note §2): take a realization by open convex sets. H5′, H6 and H7 give points
`a ∈ U_imp ∖ U_j`, `b ∈ U_jmp` and `z ∈ U_ijm`. Either `U_i` and `U_j` overlap on `[a, b]`
(Case A, `caseA_realSpace`, contradicts F_A) or they don't (Case B, `caseB_realSpace`,
contradicts H4).

`C033_not_isOpenConvex` is the corollary: C5-033 is not open-convex, because the census
(`Census.theorem1b_hyps`) checks every hypothesis of Theorem 1(b) on it.
-/

namespace RimRule

/-- **Theorem 1(b) (Rim\*).** Let `σ_i ≠ ∅`. If `C` satisfies the core hypotheses
(H1ₘ, H2ₘ, H5′, H6, H7, F_A) together with H3 and H4, then `C` is not open-convex. -/
theorem theorem1b : Theorem1b := by
  intro n C R hi hcore h3 h4 hopen
  obtain ⟨d, X, U, hR, hU⟩ := hopen
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
  · exact caseA_realSpace hR hU hi hcore.h1m hcore.fA ha haj hb hover
  · exact caseB_realSpace hR hU hi hcore.h1m hcore.h2m h3 h4 ha haj hb hz hover

/-- **Corollary.** C5-033 is not open-convex: Theorem 1(b) applies with roles
`(i,j,k,l,m,p) = (4,5,1,2,3,6)`, and the census checks every hypothesis. -/
theorem C033_not_isOpenConvex : ¬ IsOpenConvex Census.C033 := by
  obtain ⟨hi, hcore, h3, h4⟩ := Census.theorem1b_hyps
  exact theorem1b 7 Census.C033 Census.R033 hi hcore h3 h4

end RimRule
