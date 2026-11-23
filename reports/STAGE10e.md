# Stage 10e: the literal "locally good", and the counterexample with nothing cited

New files: `RimRule/Mandatory.lean` (82 lines) and `RimRule/Conj313Literal.lean` (43 lines). No existing statement changed or was deleted. Existing files changed only in the import list of `RimRule.lean` and in new lines in `Check.lean`.

## What was proved

```lean
def RimRule.IsMandatory (C : Finset (Finset (Fin n))) (σ : Finset (Fin n)) : Prop :=
  σ ∈ delta C ∧ σ.Nonempty ∧ ¬ ContractibleSpace (realization (link (delta C) σ))

def RimRule.LocallyGood (C : Finset (Finset (Fin n))) : Prop :=
  ∀ σ, IsMandatory C σ → σ ∈ C

theorem RimRule.locallyGood_iff {C : Finset (Finset (Fin n))} :
    LocallyGood C ↔ ∀ σ ∈ delta C, σ.Nonempty → σ ∉ C →
      ContractibleSpace (realization (link (delta C) σ))

theorem RimRule.LocallyGoodC.locallyGood {C : Finset (Finset (Fin n))} (h : LocallyGoodC C) :
    LocallyGood C

theorem RimRule.Rim70.all70_spec' : ∀ C ∈ all70,
    IsNeuralCode C ∧ LocallyGood C ∧ ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C

theorem RimRule.conj313_counterexample' :
    ∃ C : Finset (Finset (Fin 7)),
      IsNeuralCode C ∧ LocallyGood C ∧ ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C
```

`conj313_counterexample'` is the headline. It refutes Conjecture 3.13 of Gambacini, Jeffs, Macdonald and Shiu with the papers' own definition of locally good, and **no fact is cited**. The original `conj313_counterexample` and `all70_spec` are unchanged. The new versions follow from them through `LocallyGoodC.locallyGood`.

## Definitions and the source they mirror

The source is Gambacini, Jeffs, Macdonald, Shiu, "Non-monotonicity of closed convexity in neural codes", arXiv 1912.00963. I read **v3** (revised 2 Apr 2021), §2.2, on the arXiv HTML page.

- Just before Def 2.14, the paper recalls that a contractible set is by definition homotopy-equivalent to a single point.
- **Def 2.13 (link).** `Lk_σ(Δ) := {τ ⊂ [n] ∖ σ : σ ∪ τ ∈ Δ}`.
  - This is the existing `link K σ = {τ ∈ K : τ ∩ σ = ∅, τ ∪ σ ∈ K}`.
  - The extra condition `τ ∈ K` is automatic for a complex.
- **Def 2.14 (mandatory).** "A nonempty face σ∈Δ(𝒞) is a mandatory codeword of Δ if (the geometric realization of) Lkσ(Δ) is non-contractible."
  - This is `IsMandatory C σ`, with Δ = Δ(C).
  - "Contractible" is mathlib's `ContractibleSpace`, which means homotopy equivalent to a point.
  - It is applied to the 10a realization of the link.
- **Def 2.15 (locally good).** "A code 𝒞 is locally good if it contains every mandatory codeword of Δ(𝒞)."
  - This is `LocallyGood C`.

The docstring of `RimRule/Mandatory.lean` quotes all three definitions.

## Design choices

1. **Δ = Δ(C).** Def 2.14 is written for a general complex Δ but says "σ ∈ Δ(𝒞)". Def 2.15 applies it to Δ = Δ(𝒞), and that is the case formalized.
2. **The ambient space of the link.** The paper's link is a complex on `[n] ∖ σ`. Here it is realized inside `Fin n → ℝ`. All its faces avoid σ, so the realization lies in the coordinate subspace `ℝ^([n]∖σ)` and is the same space. Contractibility does not depend on the ambient space.
3. **The empty link.** The link of a facet is `{∅}`. Its realization is empty, so it is not contractible (10a, `not_contractibleSpace_realization_singleton_empty`). Facets are therefore mandatory, which matches the papers' convention. The paper text I read states no explicit convention for `{∅}`, and Def 2.14 only speaks of nonempty σ.
4. **Separate files.** The definitions and the implication live in `Mandatory.lean`, which is light: it imports only the topology chain. The counterexample lives in `Conj313Literal.lean`, which imports the heavy `Rim70` files. Other files can use the definitions without pulling in the 70-code certificates.
5. **Existing `.lean` files were left as they are**, following the brief's rule "New files only, plus imports".
   - The docstrings of `LocallyGood.lean` and `Conj313.lean` still describe collapsible ⇒ contractible as cited.
   - The README and LEAN_FINAL.md now say it is proved in Stage 10, and the docstrings of the new files say so as well.

## Problems hit

None. Both files compiled on the first try.

## Checks

- `lake build` passes.
- The forbidden-word scan is empty.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for:
  - `conj313_counterexample'`
  - `Rim70.all70_spec'`
  - `LocallyGoodC.locallyGood`
  - `locallyGood_iff`

## Build time

`Mandatory.lean` takes 14 s and `Conj313Literal.lean` takes 13 s (`lake build <module>`).

CI: CI_RESULT.
