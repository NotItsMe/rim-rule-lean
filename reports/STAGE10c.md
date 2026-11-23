# Stage 10c: an elementary collapse is a deformation retraction

New file: `RimRule/Collapse.lean` (292 lines). No existing file was changed apart from the import list in `RimRule.lean` and new lines in `Check.lean`. This was proved on the **first serious attempt**, so `STAGE10c_BLOCKED.md` was not needed.

## What was proved

Throughout, `K' = elemCollapse K σ τ` (that is, `K` with `σ` and `τ` removed).

```lean
/-- Hatcher's deformation retraction, verbatim in shape. -/
theorem RimRule.realization_deformationRetract {K : Finset (Finset (Fin n))}
    {σ τ : Finset (Fin n)} (hK : IsComplex K) (hf : IsFreeFace K σ τ) (hσ : σ.Nonempty) :
    ∃ H : C(unitInterval × realization K, realization K),
      (∀ x, H (0, x) = x) ∧
      (∀ x, (H (1, x) : Fin n → ℝ) ∈ realization (elemCollapse K σ τ)) ∧
      (∀ (t : unitInterval) (x : realization K),
        (x : Fin n → ℝ) ∈ realization (elemCollapse K σ τ) → H (t, x) = x)

noncomputable def RimRule.realizationCollapseHEquiv (hK : IsComplex K)
    (hf : IsFreeFace K σ τ) (hσ : σ.Nonempty) :
    ContinuousMap.HomotopyEquiv (realization K) (realization (elemCollapse K σ τ))

theorem RimRule.nonempty_hequiv_realization_elemCollapse (hK : IsComplex K)
    (hf : IsFreeFace K σ τ) (hσ : σ.Nonempty) :
    Nonempty (ContinuousMap.HomotopyEquiv (realization K) (realization (elemCollapse K σ τ)))
```

Supporting lemmas:
- `pushAlong_mem`: the homotopy stays in `|K|` for `t ∈ [0, 1]`.
- `pushAlong_one_mem`: at time 1 the point lands in `|K'|`.
- `pushAlong_of_mem_elemCollapse`: the homotopy fixes `|K'|`.
- `supp_subset_of_minOn_pos`, `eq_or_eq_of_isFreeFace` and `exists_insert_of_isFreeFace` describe free pairs.
- `mem_elemCollapse_of_not_subset`, `realization_mono` and `elemCollapse_subset` are small facts about collapses and realizations.
- `continuous_minOn` and `continuous_pushAlong` give continuity.

## The map

Write `τ = σ ∪ {w}` with `w ∉ σ`. For `x ∈ |K|`, define

- `m(x) = min_{i∈σ} x_i` (`minOn`, as mathlib's `Finset.inf'`),
- `d = |σ|·e_w − 𝟙_σ` (`pushDir`),
- `f_t(x) = x + (t·m(x))·d` (`pushAlong`).

Why this works:
- **Points with some zero coordinate in σ.** If some coordinate of `x` in σ is 0, then `m(x) = 0` and `f_t(x) = x`. This covers all of `|K'|`, together with every point whose support does not contain σ.
- **Points with m(x) > 0.** Then supp x ⊇ σ. Since σ is free, supp x is σ or τ, so x lies in the closed simplex `|τ|`. The map takes `t·m` away from each σ-coordinate and adds `|σ|·t·m` to the w-coordinate. So the sum stays 1, the coordinates stay ≥ 0 (because `t·m ≤ m ≤ x_i`), and the support stays inside τ.
- **At t = 1.** The smallest σ-coordinate becomes 0, so the support no longer contains σ, and the point is in `|K'|`.
- **The homotopy equivalence.** It uses the retraction `f_1` and the inclusion `|K'| ⊆ |K|`. The composite `f_1 ∘ incl` equals the identity exactly. `incl ∘ f_1 ≃ id` holds by the homotopy `f_t`, reversed with `Homotopic.symm`.

## Definitions mirrored

**Deformation retraction.** Hatcher, *Algebraic Topology* (quoted from memory; check the wording against a copy): "a family of maps f_t : X → X, t ∈ I, such that f_0 = 𝟙, f_1(X) = A, and f_t|A = 𝟙 for all t", continuous as a map X × I → X.
- `realization_deformationRetract` states this with `f_1(X) ⊆ A`.
- Together with `f_t|A = 𝟙` that gives `f_1(X) = A`.

**New definitions.** All are auxiliary; none is a new mathematical notion:
- `minOn σ hσ x = σ.inf' hσ (x ·)`
- `pushDir σ w`
- `pushAlong σ hσ w t x`
- `realizationCollapseHEquiv`, which is data of mathlib's type `ContinuousMap.HomotopyEquiv`.

The geometric idea is the standard "push the open simplex τ off the free face σ". The docstring cites Cohen, *A Course in Simple-Homotopy Theory*, and Kozlov, *Combinatorial Algebraic Topology*.

## Design choices

- **One global formula instead of a pasting argument.** The brief suggested defining the push on τ and gluing it to the identity elsewhere with the pasting lemma. Instead, `m(x)` vanishes exactly where the map must be the identity, so one formula works on all of `|K|`. No closed-set pasting is needed, and continuity is one line (`Continuous.finset_inf'_apply`).
- **Straight-line push instead of radial projection from the barycentre of σ.** The textbook picture projects radially from just outside the barycentre of σ. The map used here moves points in a fixed direction `d` by an amount `m(x)`. It is also a deformation retraction of `|τ|` onto `∂τ ∖ (open star of σ)`, and it is piecewise linear and easier to check in Lean.
- **σ ≠ ∅ is a hypothesis.** It is needed: if σ = ∅ then K = {∅, {w}}, so `|K|` is a point while `|K'|` is empty. In 10d it is discharged because `∅` survives to the end of the collapse sequence.
- **IsComplex K is a hypothesis.** It is used to put `f_t(x)` back into `|K|` (the support is a subset of τ ∈ K).

## Problems hit and how they were solved

1. **Name clash.** `open unitInterval` brings in the notation `σ` for `unitInterval.symm`, so every variable named `σ` broke. Fixed by not opening the namespace and writing `unitInterval` in full.
2. **Notation not in scope.** The notation `≃ₕ` was not available without opening `ContinuousMap`. Used `ContinuousMap.HomotopyEquiv X Y` explicitly.
3. **Binder type.** In `∀ t x, (x : Fin n → ℝ) ∈ … → H (t, x) = x`, the type ascription fixed the type of `x` to `Fin n → ℝ` rather than `realization K`. Fixed by giving binder types explicitly.
4. **Unused section variables.** The linter flagged two lemmas that did not use `hK`, `hw` or `hτ`. Fixed with `omit … in`, and the call sites were updated.

## Checks

- `lake build` passes.
- The forbidden-word scan is empty.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for:
  - `realization_deformationRetract`
  - `nonempty_hequiv_realization_elemCollapse`
  - `realizationCollapseHEquiv`
  - `pushAlong_mem`
  - `pushAlong_one_mem`
  - `pushAlong_of_mem_elemCollapse`

## Build time

`Collapse.lean` takes 26–41 s with `lake env lean` (the spread is RAM pressure), and 30 s with `lake build RimRule.Collapse`.

CI: GitHub Actions run 45104031484 on commit e86e33f passed (`lake build`, 2 min 5 s).
