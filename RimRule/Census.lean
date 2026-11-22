import RimRule.Defs

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Census: the hypotheses of Theorem 1(b) hold on C5-033

Non-vacuity check: the code C5-033 satisfies every hypothesis of Theorem 1(b)
(and F_B, so also every hypothesis of Theorem 1(a)) with roles
`(i,j,k,l,m,p) = (4,5,1,2,3,6)`. Every fact is checked by `decide` (kernel evaluation;
no `native_decide`).

Data source: `data/C5-033.md`, copied from github.com/NotItsMe/neural-codes-96,
`data/codes.json`, id C5-033. Neurons keep their paper labels 1..6: we use `Fin 7`
and leave neuron 0 unused (it lies in no codeword and in no role).
-/

namespace RimRule.Census

/-- C5-033, all 13 codewords, exactly as listed in `data/C5-033.md`. -/
def C033 : Finset (Finset (Fin 7)) :=
  {∅, {1}, {2}, {3}, {1,2}, {3,6}, {1,3,4}, {2,3,5}, {3,4,5},
   {1,3,4,5}, {1,3,4,6}, {2,3,4,5}, {2,3,5,6}}

/-- Roles `(i,j,k,l,m,p) = (4,5,1,2,3,6)`, each a single neuron. -/
def R033 : Roles 7 where
  i := {4}
  j := {5}
  k := {1}
  l := {2}
  m := {3}
  p := {6}

/-! ### Sanity checks on the data -/

/-- 13 distinct codewords, as in the source. -/
theorem card_C033 : C033.card = 13 := by decide +kernel

/-- The maximal codewords listed in the source: 12, 1345, 1346, 2345, 2356. -/
def facets033 : Finset (Finset (Fin 7)) :=
  {{1,2}, {1,3,4,5}, {1,3,4,6}, {2,3,4,5}, {2,3,5,6}}

/-- Each listed facet is a codeword, every codeword lies under a listed facet, and no
listed facet lies strictly under another codeword. So they are exactly the maximal
codewords. -/
theorem facets033_correct :
    facets033 ⊆ C033 ∧
    (∀ c ∈ C033, ∃ f ∈ facets033, c ⊆ f) ∧
    (∀ f ∈ facets033, ∀ c ∈ C033, f ⊆ c → c = f) := by decide +kernel

/-- `∅ ∈ C`, so C5-033 is a neural code in the paper's sense. -/
theorem isNeuralCode_C033 : IsNeuralCode C033 := by decide +kernel

/-! ### The hypotheses, one by one -/

theorem i_nonempty : R033.i.Nonempty := ⟨4, by decide⟩

theorem h1m : H1m C033 R033 := by decide +kernel
theorem h2m : H2m C033 R033 := by decide +kernel
theorem h3 : H3 C033 R033 := by decide +kernel
theorem h4 : H4 C033 R033 := by decide +kernel
theorem h5' : H5' C033 R033 := by decide +kernel
theorem h6 : H6 C033 R033 := by decide +kernel
theorem h7 : H7 C033 R033 := by decide +kernel
theorem fA : FA C033 R033 := by decide +kernel
theorem fB : FB C033 R033 := by decide +kernel

theorem core : Core C033 R033 := ⟨h1m, h2m, h5', h6, h7, fA⟩

/-- **Non-vacuity of Theorem 1(b):** C5-033 meets every hypothesis of `Theorem1b`. -/
theorem theorem1b_hyps : R033.i.Nonempty ∧ Core C033 R033 ∧ H3 C033 R033 ∧ H4 C033 R033 :=
  ⟨i_nonempty, core, h3, h4⟩

/-- **Non-vacuity of Theorem 1(a):** C5-033 meets every hypothesis of `Theorem1a`. -/
theorem theorem1a_hyps : R033.i.Nonempty ∧ Core C033 R033 ∧ FB C033 R033 :=
  ⟨i_nonempty, core, fB⟩

/-! ### Negative controls

The checks are not trivially true: small changes break them. Dropping the apex
(`m = ∅`) breaks H4, because the codeword `{1,2}` then contains k, l and m. Dropping
`{1,3,4,6}` removes the only H5′ witness. -/

theorem control_no_apex : ¬ H4 C033 { R033 with m := ∅ } := by decide +kernel

theorem control_drop_1346 : ¬ H5' (C033.erase {1,3,4,6}) R033 := by decide +kernel

end RimRule.Census
