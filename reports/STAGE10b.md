# Stage 10b: the realization of a cone is contractible

New file: `RimRule/Cone.lean` (80 lines). No existing file changed except the import list in `RimRule.lean` and new lines in `Check.lean`.

## What was proved

```lean
theorem RimRule.vtx_mem_realization {K : Finset (Finset (Fin n))} {v : Fin n} (h : {v} ∈ K) :
    vtx v ∈ realization K

theorem RimRule.supp_smul_vtx_add_smul_subset (v : Fin n) (x : Fin n → ℝ) (a b : ℝ) :
    supp (a • vtx v + b • x) ⊆ insert v (supp x)

theorem RimRule.starConvex_realization_cone {K : Finset (Finset (Fin n))} {v : Fin n}
    (hK : IsComplex K) (hc : IsConeWith K v) : StarConvex ℝ (vtx v) (realization K)

theorem RimRule.contractibleSpace_realization_cone {K : Finset (Finset (Fin n))} {v : Fin n}
    (hK : IsComplex K) (h0 : ∅ ∈ K) (hc : IsConeWith K v) :
    ContractibleSpace (realization K)

theorem RimRule.contractibleSpace_realization_link_of_hull_ne {C : Finset (Finset (Fin n))}
    {σ : Finset (Fin n)} (hΔ : σ ∈ delta C) (h : hull C σ ≠ σ) :
    ContractibleSpace (realization (link (delta C) σ))
```

Main theorem: `contractibleSpace_realization_cone`. The last theorem is a corollary: a face of Δ(C) that is not its own hull has a contractible link, because that link is a cone (`isConeWith_link_delta`, Stage 9).

## Proof

For a cone with apex `v` and a point `x ∈ |K|`, every point `a • e_v + b • x` of the segment from `e_v` to `x` has nonnegative coordinates summing to 1. Its support lies inside `{v} ∪ supp x`, which is a face because `K` is a cone. Since `K` is a complex, the support is a face too. So `|K|` is star-convex around `e_v`. mathlib's `StarConvex.contractibleSpace` (`Mathlib/Analysis/Convex/Contractible.lean`) then gives contractibility. Nonemptiness comes from `e_v ∈ |K|`, because `{v} = insert v ∅ ∈ K`.

## New definitions

None. `IsConeWith` (Stage 9) and `realization` (Stage 10a) are reused. The textbook fact mirrored is that a cone deformation retracts to its apex (Hatcher, *Algebraic Topology*, Ch. 0). That citation was written from memory and should be checked against a copy.

## Design choices

- I searched mathlib first, as the brief asks. `StarConvex.contractibleSpace` already exists, so no contractibility lemma was written.
- The hypotheses match `collapsible_of_cone` (Stage 9): `IsComplex K`, `∅ ∈ K`, `IsConeWith K v`.

## Problems hit

- `hiv ▸ mem_insert_self v _` rewrote in the wrong direction. Replaced it with `rw [hiv]; exact mem_insert_self v _`.
- **Unrelated rebuild.** The public-release commit (871c176) edited the module docstring of `Defs.lean`, which every file imports, so the whole project had to be rebuilt locally. The first parallel `lake build` failed with `failed to read file …olean.private` on three modules. With only about 150 MB of RAM free, this was the same out-of-memory failure as in Stage 9. Rebuilding one module at a time (`lake build <module>`, in dependency order) worked.

## Checks

- `lake build` passes. The only warnings are the usual "consider adding `module`" notes.
- The forbidden-word scan (`sorry`, `admit`, `native_decide`, `axiom`) over the new file returns nothing.
- `lake env lean Check.lean` prints `[propext, Classical.choice, Quot.sound]` for `starConvex_realization_cone`, `contractibleSpace_realization_cone` and `contractibleSpace_realization_link_of_hull_ne`, and for every earlier theorem.

## Build time

`Cone.lean` takes 23 s on its own (`lake env lean`) and 24 s inside `lake build`. The one-module-at-a-time rebuild of the whole project (forced by the `Defs.lean` docstring change) took 29 min 20 s (1760 s; Links1 388 s and Links2 657 s are most of it).

CI: CI_RESULT.
