# Stage 10 summary: collapsible ⇒ contractible is proved, and nothing is cited

## Result

Conjecture 3.13 of Gambacini, Jeffs, Macdonald and Shiu (arXiv 1912.00963) is refuted in Lean. The refutation uses the papers' own definition of "locally good" and **no cited fact**:

```lean
theorem RimRule.conj313_counterexample' :
    ∃ C : Finset (Finset (Fin 7)),
      IsNeuralCode C ∧ LocallyGood C ∧ ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C

theorem RimRule.Rim70.all70_spec' : ∀ C ∈ all70,
    IsNeuralCode C ∧ LocallyGood C ∧ ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C
```

`LocallyGood` is Def 2.15 of the paper, with "mandatory" from Def 2.14. A face is mandatory when it is nonempty, lies in Δ(C), and its link has a non-contractible geometric realization. Both theorems use only `[propext, Classical.choice, Quot.sound]`. The Stage 9 statements (`conj313_counterexample` and `all70_spec`, with `LocallyGoodC`) were not changed.

## The chain

| Sub-stage | File | Main statement | Report |
|---|---|---|---|
| 10a | `Realization.lean` | `realization K = {x ≥ 0, ∑ x = 1, supp x ∈ K}`; sanity checks (`\|{∅}\| = ∅`, a vertex is a point, a simplex is convex) | PROGRESS.md |
| 10b | `Cone.lean` | `contractibleSpace_realization_cone`: a cone's realization is star-convex, hence contractible | `STAGE10b.md` |
| 10c | `Collapse.lean` | `realization_deformationRetract` and `realizationCollapseHEquiv`: an elementary collapse is a deformation retraction | `STAGE10c.md` |
| 10d | `CollapsibleContractible.lean` | `contractibleSpace_realization_of_collapsible`: collapsible ⇒ contractible | `STAGE10d.md` |
| 10e | `Mandatory.lean`, `Conj313Literal.lean` | `LocallyGood` and `IsMandatory` (Def 2.14–2.15), `LocallyGoodC.locallyGood`, `conj313_counterexample'` | `STAGE10e.md` |

## Key idea (10c)

Take a free pair (σ, τ = σ ∪ {w}) with σ ≠ ∅. Define

- `m(x) = min_{i∈σ} x_i`,
- `f_t(x) = x + t·m(x)·(|σ| e_w − 𝟙_σ)`.

This single continuous formula is a deformation retraction of |K| onto |K ∖ {σ, τ}|. It is the identity wherever `m = 0`, which includes every point outside the open star of σ. So no pasting lemma is needed.

10c, the step the brief called hard, was proved on the first attempt. The stop rule and `STAGE10c_BLOCKED.md` were not needed.

## Design choices logged

- **Realization (10a):** defined by support, not as a union of simplices. It is proved equal to the textbook union `⋃ conv{eᵢ}`.
- **σ ≠ ∅:** a hypothesis in 10c. In 10d it is derived, because `∅` survives to the final `{∅, {v}}`.
- **The collapse map:** a straight-line push with one global formula, instead of radial projection plus pasting.
- **10e:**
  - Δ = Δ(C) in Def 2.14.
  - The link is realized in `ℝⁿ`; it lies in the coordinate subspace `ℝ^([n]∖σ)`.
  - The realization of `{∅}` is empty, so facets are mandatory.
- **Existing `.lean` files:** none was edited apart from the import list in `RimRule.lean` and new lines in `Check.lean`, following the brief's rule "new files only".
  - The old docstrings of `LocallyGood.lean` and `Conj313.lean` still call collapsible ⇒ contractible "cited".
  - README.md and LEAN_FINAL.md now say it is proved.

## Checks (final state)

- `lake build` passes (3450 jobs). The only warnings are "consider adding `module`".
- No `sorry`, `admit`, `native_decide` or `axiom` in any new file.
- `lake env lean Check.lean`: all 39 `#print axioms` lines are exactly `[propext, Classical.choice, Quot.sound]`.
- CI was green after every sub-stage:

| Sub-stage | Run | Commit | Time |
|---|---|---|---|
| 10b | 45103662434 | 5557cc7 | 1 min 34 s |
| 10c | 45104031484 | e86e33f | 2 min 5 s |
| 10d | 45104413493 | 0f1895e | 1 min 38 s |
| 10e | 45104819300 | 4865f7a | 1 min 42 s |

## Build times

| File | Time |
|---|---|
| `Cone.lean` | 23 s |
| `Collapse.lean` | 16–41 s |
| `CollapsibleContractible.lean` | 18 s |
| `Mandatory.lean` | 14 s |
| `Conj313Literal.lean` | 9–13 s |

The new Stage 10b–e files add under 2 minutes to a build.

One full local rebuild was forced by the public-release commit's docstring edit in `Defs.lean`. It took 29 min 20 s, building one module at a time because only about 150 MB of RAM was free.

## Line count (new in 10b–e)

| File | Lines |
|---|---|
| Cone | 75 |
| Collapse | 292 |
| CollapsibleContractible | 94 |
| Mandatory | 82 |
| Conj313Literal | 43 |
| **Total** | **586** |

## Still not checked by Lean

- The 70 codes are pairwise non-isomorphic. This is checked in Python only; `all70_nodup` proves only that they are distinct as sets.
- Whether Conjecture 3.13 had already been refuted elsewhere. No full literature review was done.
- Textbook citations in docstrings (Hatcher, Munkres, Matoušek, Cohen, Kozlov) give author and title only; page and chapter numbers were removed because they were written from memory. The quoted wording of Hatcher's definitions should still be checked against a copy. Def 2.13–2.15 of 1912.00963 were read from arXiv v3.
