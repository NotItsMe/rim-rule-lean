import RimRule.CollapsibleContractible

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Mandatory codewords and locally good codes, literally (Stage 10e)

The papers' definitions, with contractibility of the geometric realization (Stage 10a) in
place of the combinatorial stand-in `LocallyGoodC`.

## The definitions mirrored

Gambacini, Jeffs, Macdonald, Shiu, "Non-monotonicity of closed convexity in neural codes",
arXiv 1912.00963 (v3), §2.2. Just before Definition 2.14 they recall that "a contractible
set, by definition, is homotopy-equivalent to a single point."

* **Definition 2.13** (link). "Let Δ be a simplicial complex on [n] and let σ ∈ Δ. The link
  of σ in Δ is: Lk_σ(Δ) := {τ ⊂ [n] ∖ σ : σ ∪ τ ∈ Δ}." This is `link K σ` of
  `RimRule/Complex.lean` (`τ` disjoint from `σ` with `τ ∪ σ ∈ K`; the extra condition `τ ∈ K`
  there is automatic for a complex).
* **Definition 2.14** (mandatory). "Let Δ be a simplicial complex. A nonempty face σ ∈ Δ(𝒞)
  is a mandatory codeword of Δ if (the geometric realization of) Lk_σ(Δ) is non-contractible.
  Otherwise, σ is non-mandatory." Here Δ = Δ(C), and this is `IsMandatory C σ`:
  `σ ∈ Δ(C)`, `σ ≠ ∅`, and `¬ ContractibleSpace |Lk_σ(Δ(C))|`.
* **Definition 2.15** (locally good). "A code 𝒞 is locally good if it contains every mandatory
  codeword of Δ(𝒞)." This is `LocallyGood C`.

Contractible is mathlib's `ContractibleSpace` (homotopy equivalent to a point), applied to
`realization (link (delta C) σ)` with the subspace topology from `Fin n → ℝ`. The link avoids
`σ`, so its realization lies in the coordinate subspace `ℝ^([n] ∖ σ)`, exactly as if it were
realized on the vertex set `[n] ∖ σ`. The link of a facet is `{∅}`, whose realization is
empty and hence not contractible (`not_contractibleSpace_realization_singleton_empty`), so
facets are mandatory, as in the papers.

## What is proved

* `LocallyGoodC.locallyGood : LocallyGoodC C → LocallyGood C`. Every nonempty non-codeword face
  has a collapsible link (`LocallyGoodC`), a collapsible complex has contractible realization
  (`contractibleSpace_realization_of_collapsible`, Stage 10d), so no such face is mandatory.
  This replaces the cited fact of Stages 8–9 with a proof.
* `locallyGood_iff`: the equivalent form "every nonempty `σ ∈ Δ(C) ∖ C` has a contractible
  link".
-/

namespace RimRule

open Finset

variable {n : ℕ}

/-- **Mandatory codeword** (Gambacini–Jeffs–Macdonald–Shiu, Def 2.14): a nonempty face
`σ ∈ Δ(C)` whose link `Lk_σ(Δ(C))` has non-contractible geometric realization. -/
def IsMandatory (C : Finset (Finset (Fin n))) (σ : Finset (Fin n)) : Prop :=
  σ ∈ delta C ∧ σ.Nonempty ∧ ¬ ContractibleSpace (realization (link (delta C) σ))

/-- **Locally good** (Gambacini–Jeffs–Macdonald–Shiu, Def 2.15): `C` contains every mandatory
codeword of `Δ(C)`. -/
def LocallyGood (C : Finset (Finset (Fin n))) : Prop :=
  ∀ σ, IsMandatory C σ → σ ∈ C

/-- Equivalent form: every nonempty face of `Δ(C)` that is not a codeword has a contractible
link. -/
theorem locallyGood_iff {C : Finset (Finset (Fin n))} :
    LocallyGood C ↔ ∀ σ ∈ delta C, σ.Nonempty → σ ∉ C →
      ContractibleSpace (realization (link (delta C) σ)) := by
  constructor
  · intro h σ hΔ hne hσ
    by_contra hc
    exact hσ (h σ ⟨hΔ, hne, hc⟩)
  · rintro h σ ⟨hΔ, hne, hc⟩
    by_contra hσ
    exact hc (h σ hΔ hne hσ)

/-- **`LocallyGoodC` implies locally good**, with nothing cited: a collapsible link is
contractible (Stage 10d). -/
theorem LocallyGoodC.locallyGood {C : Finset (Finset (Fin n))} (h : LocallyGoodC C) :
    LocallyGood C :=
  locallyGood_iff.2 fun σ hΔ hne hσ =>
    contractibleSpace_realization_link_of_collapsible (h σ hΔ hne hσ)

end RimRule
