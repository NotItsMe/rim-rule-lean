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

**The one cited fact.** `LocallyGoodC C` (every nonempty non-codeword face of `Δ(C)` has a
*collapsible* link) implies "locally good" (Def 2.14–2.15: every such face has a
*contractible* link) by the textbook fact collapsible ⇒ contractible. That fact is not proved
in Lean (see `RimRule/LocallyGood.lean`). Everything else is.
-/

namespace RimRule

open Rim70

/-- **Refutes Conjecture 3.13 of Gambacini–Jeffs–Macdonald–Shiu** (arXiv 1912.00963), modulo
the single cited fact collapsible ⇒ contractible: there is a neural code on 7 neurons that
satisfies `LocallyGoodC` (hence is locally good, by that fact) and is neither open-convex nor
closed-convex. -/
theorem conj313_counterexample :
    ∃ C : Finset (Finset (Fin 7)),
      IsNeuralCode C ∧ LocallyGoodC C ∧ ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C :=
  ⟨FiveFac399, all70_spec FiveFac399 List.mem_cons_self⟩

end RimRule
