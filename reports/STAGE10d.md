# Stage 10d: collapsible ⇒ contractible

New file: `RimRule/CollapsibleContractible.lean` (94 lines). No existing file changed except the import list in `RimRule.lean` and new lines in `Check.lean`.

## What was proved

```lean
theorem RimRule.contractibleSpace_realization_of_collapsible {K : Finset (Finset (Fin n))}
    (hK : IsComplex K) (h : Collapsible K) : ContractibleSpace (realization K)

theorem RimRule.contractibleSpace_realization_link_of_collapsible {C : Finset (Finset (Fin n))}
    {σ : Finset (Fin n)} (h : Collapsible (link (delta C) σ)) :
    ContractibleSpace (realization (link (delta C) σ))

theorem RimRule.nonempty_hequiv_of_collapsesTo : ∀ (K : Finset (Finset (Fin n)))
    (steps : List (Finset (Fin n) × Finset (Fin n))) (L : Finset (Finset (Fin n))),
    IsComplex K → CollapsesTo K steps L → ∅ ∈ L →
      Nonempty (ContinuousMap.HomotopyEquiv (realization K) (realization L))

theorem RimRule.isComplex_elemCollapse {K : Finset (Finset (Fin n))} {σ τ : Finset (Fin n)}
    (hK : IsComplex K) (hf : IsFreeFace K σ τ) : IsComplex (elemCollapse K σ τ)

theorem RimRule.collapsesTo_subset :
    CollapsesTo K steps L → L ⊆ K

theorem RimRule.ssubset_of_isFreeFace (hf : IsFreeFace K σ τ) : σ ⊂ τ
```

The main theorem is `contractibleSpace_realization_of_collapsible`. This is the fact that Stages 8 and 9 cited without proof.

## Proof

The proof is structural recursion on the list of collapses, with `K` generalized.

- **Empty list.** `K = L`, and the homotopy equivalence is `HomotopyEquiv.refl`.
- **Step `(σ, τ) :: rest`.**
  - Because `∅ ∈ L` and collapsing only removes faces (`collapsesTo_subset`), `∅` is still in `elemCollapse K σ τ`. So `σ ≠ ∅`, which is the side condition 10c needs.
  - `elemCollapse K σ τ` is again a complex (`isComplex_elemCollapse`).
  - Compose `realizationCollapseHEquiv` (10c) with the recursive equivalence using `HomotopyEquiv.trans`.
- **Collapsible.** The target is `{∅, {v}}`, which contains `∅`. Its realization is the single point `e_v` (`contractibleSpace_realization_vertex`, 10a). mathlib's `ContinuousMap.HomotopyEquiv.contractibleSpace` transfers contractibility back to `|K|`.

## New definitions

None.

## Design choices

- **`IsComplex K` is a hypothesis.** `Collapsible` from Stage 8 does not require `K` to be a complex, but the geometric argument needs one. Every complex this project uses is a link in `Δ(C)`, and `isComplex_link` covers all of them.
- **The nonempty-free-face condition is derived, not assumed.** A general `CollapsesTo` could remove `∅` (the free pair `(∅, {w})`). That cannot happen in a sequence ending at `{∅, {v}}`, and `collapsesTo_subset` shows this.

## Problems hit

None. The file compiled on the first try. The only follow-up was the style linter preferring `have` over `haveI` for a `Prop` instance.

## Checks

- `lake build` passes.
- The forbidden-word scan is empty.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for:
  - `contractibleSpace_realization_of_collapsible`
  - `contractibleSpace_realization_link_of_collapsible`
  - `nonempty_hequiv_of_collapsesTo`
  - `isComplex_elemCollapse`
  - `collapsesTo_subset`

## Build time

`CollapsibleContractible.lean` takes 19 s (`lake build RimRule.CollapsibleContractible`).

CI: CI_RESULT.
