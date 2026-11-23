import RimRule.Conj313
import RimRule.Mandatory

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Conjecture 3.13 counterexample with the literal "locally good" (Stage 10e)

Gambacini, Jeffs, Macdonald, Shiu (arXiv 1912.00963), Conjecture 3.13: every locally good code
on at most 7 neurons is open convex or closed convex.

`conj313_counterexample'` and `Rim70.all70_spec'` restate `conj313_counterexample` and
`Rim70.all70_spec` with the papers' definition `LocallyGood` (Def 2.14–2.15, contractible
links of geometric realizations, `RimRule/Mandatory.lean`) in place of `LocallyGoodC`. The
step between them, `LocallyGoodC.locallyGood`, is proved, so **no fact is cited**. The
original statements are unchanged.
-/

namespace RimRule

namespace Rim70

/-- All 70 codes are neural codes, locally good in the papers' sense (Def 2.15), and neither
open convex nor closed convex. -/
theorem all70_spec' : ∀ C ∈ all70,
    IsNeuralCode C ∧ LocallyGood C ∧ ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C := by
  intro C hC
  obtain ⟨h1, h2, h3, h4⟩ := all70_spec C hC
  exact ⟨h1, h2.locallyGood, h3, h4⟩

end Rim70

/-- **Refutes Conjecture 3.13 of Gambacini–Jeffs–Macdonald–Shiu** (arXiv 1912.00963), with no
cited fact: there is a neural code on 7 neurons that is locally good (Def 2.14–2.15, with
contractibility of geometric realizations) and is neither open convex nor closed convex. -/
theorem conj313_counterexample' :
    ∃ C : Finset (Finset (Fin 7)),
      IsNeuralCode C ∧ LocallyGood C ∧ ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C := by
  obtain ⟨C, h1, h2, h3, h4⟩ := conj313_counterexample
  exact ⟨C, h1, h2.locallyGood, h3, h4⟩

end RimRule
