import RimRule.Rim70.Summary

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# A counterexample to Conjecture 3.13 of Gambacini–Jeffs–Macdonald–Shiu

Gambacini, Jeffs, Macdonald, Shiu, "Non-monotonicity of closed convexity in neural codes"
(arXiv 1912.00963), Conjecture 3.13: every locally good code on at most 7 neurons is
open-convex or closed-convex.

`conj313_counterexample` gives a code on 7 neurons (neuron 0 silent, the others 1..6) that is
a neural code, satisfies `LocallyGoodC`, and is neither open-convex nor closed-convex. The
witness is `Rim70.FiveFac399`; `Rim70.all70_spec` proves the same for all 70 codes in
`Rim70.all70`.

**Collapsible ⇒ contractible (now proved).** `LocallyGoodC C` (every nonempty non-codeword
face of `Δ(C)` has a *collapsible* link) implies "locally good" (Def 2.14–2.15: every such face
has a *contractible* link) by collapsible ⇒ contractible. That fact was cited up to Stage 9; it
is proved in Stage 10d (`RimRule/CollapsibleContractible.lean`). The version of this theorem
with the papers' `LocallyGood` and nothing cited is `conj313_counterexample'`
(`RimRule/Conj313Literal.lean`).
-/

namespace RimRule

open Rim70

/-- **Refutes Conjecture 3.13 of Gambacini–Jeffs–Macdonald–Shiu** (arXiv 1912.00963): there
is a neural code on 7 neurons that satisfies `LocallyGoodC` (hence is locally good, by
collapsible ⇒ contractible, proved in Stage 10d) and is neither open-convex nor closed-convex.
See `conj313_counterexample'` for the form stated with `LocallyGood`. -/
theorem conj313_counterexample :
    ∃ C : Finset (Finset (Fin 7)),
      IsNeuralCode C ∧ LocallyGoodC C ∧ ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C :=
  ⟨FiveFac399, all70_spec FiveFac399 List.mem_cons_self⟩

end RimRule
