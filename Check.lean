import RimRule

-- Run with: lake env lean Check.lean
#check @RimRule.conj313_counterexample
#check @RimRule.Rim70.all70_spec
#check @RimRule.Rim70.all70_nodup
#check @RimRule.LocallyGoodC
#check @RimRule.theorem1b
#print axioms RimRule.conj313_counterexample
#print axioms RimRule.Rim70.all70_spec
#print axioms RimRule.Rim70.all70_nodup
#print axioms RimRule.Rim70.length_all70
#print axioms RimRule.locallyGoodC_of_certOK
#print axioms RimRule.collapsible_of_cone
#print axioms RimRule.collapsible_link_of_hull_ne
#print axioms RimRule.LocallyGoodC.linksCollapsible
#print axioms RimRule.theorem1b
#print axioms RimRule.theorem1b_open
#print axioms RimRule.theorem1a
#print axioms RimRule.C033_not_isOpenConvex
#print axioms RimRule.C033_not_isClosedConvex
-- Stage 10a: geometric realization
#check @RimRule.realization
#print axioms RimRule.realization_singleton_empty
#print axioms RimRule.not_contractibleSpace_realization_singleton_empty
#print axioms RimRule.realization_vertex
#print axioms RimRule.contractibleSpace_realization_vertex
#print axioms RimRule.realization_powerset
#print axioms RimRule.realization_powerset_eq_convexHull
#print axioms RimRule.contractibleSpace_realization_powerset
#print axioms RimRule.realization_eq_iUnion_convexHull
