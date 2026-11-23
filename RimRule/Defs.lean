import Mathlib.Analysis.Convex.Topology

-- This project is not part of mathlib, so the mathlib copyright-header linter does not apply.
set_option linter.style.header false

/-!
# Definitions for Theorem 1 (the Rim rule)

This file mirrors the definitions of the paper write-up line by line
(source: the author's unpublished note "Rim Theorem Upgrade, part 2" (2026-11-20),
§5 "Definitions" and "Theorem 1", with the fixes from an unpublished referee report
on Theorem 1).

It contains only definitions, the decidability instances needed for the census
(`decide`), the "basic fact" from §5, and the two target statements as `Prop`s.
No proofs of the theorem live here.

## Conventions
* Neurons are `Fin n`, so `[n] = {0, …, n-1}` (the paper's `{1, …, n}` shifted by one).
* A codeword is a `Finset (Fin n)`; a code is a `Finset (Finset (Fin n))`.
* `ℝ^d` is `Fin d → ℝ`. It has the usual topology and vector-space structure, so
  "open" and "convex" mean exactly what they mean in the paper.
* "A codeword contains t" means `σ_t ⊆ c`. Role sets may be empty and may overlap.
-/

namespace RimRule

open Set

/-! ### Neural codes -/

/-- Paper: "A **neural code** is `C ⊆ 2^[n]` with `∅ ∈ C`." (This quotes the council note.
Gambacini et al. Def 2.1 and Chan et al. Def 2.1 do not require `∅ ∈ C`; Chan et al. add it as
Assumption 2.5. Asking for it only makes a statement "`C` is a neural code and …" stronger.) -/
def IsNeuralCode {n : ℕ} (C : Finset (Finset (Fin n))) : Prop :=
  ∅ ∈ C

instance {n : ℕ} (C : Finset (Finset (Fin n))) : Decidable (IsNeuralCode C) := by
  unfold IsNeuralCode; infer_instance

/-! ### Realizations

Paper: "A **realization** consists of sets `U₁,…,Uₙ ⊆ X ⊆ ℝ^d` with
`C = {c(x) : x ∈ X}`, where `c(x) = {s : x ∈ U_s}`." This is the code of a realization,
Chan et al. Def 2.3 (Gambacini et al. Def 2.3). Those papers state it with atoms: `σ` is a
codeword iff `U_σ ∖ ⋃_{j∉σ} U_j ≠ ∅`, with `U_∅ := X`. A point `x` lies in that atom exactly
when `x ∈ X` and `c(x) = σ` (for `σ ≠ ∅`, `x ∈ X` follows from `U_i ⊆ X`), so the two forms
agree whenever every `U_s ⊆ X`, which `IsRealization` requires. Open/closed convexity
(Def 2.4 in both papers) is `IsOpenConvex` / `IsClosedConvex` below.

The ambient space is an arbitrary type `E`; the theorem statements below
specialise it to `ℝ^d = Fin d → ℝ`. -/

section Realization

variable {E : Type*} {n : ℕ}

/-- Paper: `c(x) = {s : x ∈ U_s}`, the codeword of the point `x`. -/
noncomputable def codeword (U : Fin n → Set E) (x : E) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun s => x ∈ U s)

/-- Paper: `U_σ = ⋂_{s∈σ} U_s`, with `U_∅ = ℝ^d` (here `univ`, automatically).

The published papers (Chan et al. Def 2.3, Gambacini et al. Def 2.3) instead set
`U_∅ := X`. For a general stimulus space `X`, `univ ≠ X`, but this is **harmless**:
* the code of a realization is defined by `codeOf X U = c '' X` (points of `X` only), not
  through `inter`, so the convention never enters the definitions of `IsOpenConvex` and
  `IsClosedConvex`;
* for `σ ≠ ∅` the two conventions agree, since `U_s ⊆ X`;
* `inter` appears in no statement (not in `IsRealization`, `IsOpenConvex`, `IsClosedConvex`,
  the hypotheses, `Theorem1a` or `Theorem1b`), only inside proofs, which Lean checks. So the
  convention cannot change what any theorem says. -/
def inter (U : Fin n → Set E) (σ : Finset (Fin n)) : Set E :=
  ⋂ s ∈ σ, U s

/-- Paper: the code of a realization, `{c(x) : x ∈ X}`. -/
noncomputable def codeOf (X : Set E) (U : Fin n → Set E) : Set (Finset (Fin n)) :=
  codeword U '' X

/-- Paper: `U₁,…,Uₙ ⊆ X` and `C = {c(x) : x ∈ X}`. -/
structure IsRealization (C : Finset (Finset (Fin n))) (X : Set E) (U : Fin n → Set E) :
    Prop where
  subset : ∀ s, U s ⊆ X
  code_eq : (C : Set (Finset (Fin n))) = codeOf X U

/-- Paper §5: "For `x ∈ X`, `x ∈ U_σ ⇔ c(x) ⊇ σ`." (Holds for every `x`, in fact.) -/
theorem mem_inter_iff_subset_codeword (U : Fin n → Set E) (σ : Finset (Fin n)) (x : E) :
    x ∈ inter U σ ↔ σ ⊆ codeword U x := by
  classical
  simp [inter, codeword, Finset.subset_iff]

end Realization

/-- `ℝ^d`, as used in the paper. -/
abbrev RealSpace (d : ℕ) : Type := Fin d → ℝ

/-- Paper: "C is **open-convex** if it has a realization by convex open sets."
The stimulus space `X ⊆ ℝ^d` is arbitrary, as in Chan et al. Def 2.4. -/
def IsOpenConvex {n : ℕ} (C : Finset (Finset (Fin n))) : Prop :=
  ∃ (d : ℕ) (X : Set (RealSpace d)) (U : Fin n → Set (RealSpace d)),
    IsRealization C X U ∧ ∀ s, IsOpen (U s) ∧ Convex ℝ (U s)

/-- Paper: "C is **closed-convex** if it has a realization by convex closed sets." -/
def IsClosedConvex {n : ℕ} (C : Finset (Finset (Fin n))) : Prop :=
  ∃ (d : ℕ) (X : Set (RealSpace d)) (U : Fin n → Set (RealSpace d)),
    IsRealization C X U ∧ ∀ s, IsClosed (U s) ∧ Convex ℝ (U s)

/-! ### Role assignments and the hypotheses -/

/-- Paper: "A **role assignment** is six sets `σ_i, σ_j, σ_k, σ_l, σ_m, σ_p ⊆ [n]`,
which may overlap or be empty." -/
structure Roles (n : ℕ) where
  i : Finset (Fin n)
  j : Finset (Fin n)
  k : Finset (Fin n)
  l : Finset (Fin n)
  m : Finset (Fin n)
  p : Finset (Fin n)

section Hypotheses

variable {n : ℕ} (C : Finset (Finset (Fin n))) (R : Roles n)

/-- **H1ₘ**: every codeword containing i and m but not j contains k. -/
def H1m : Prop :=
  ∀ c ∈ C, R.i ∪ R.m ⊆ c → ¬ R.j ⊆ c → R.k ⊆ c

/-- **H2ₘ**: every codeword containing j and m but not i contains l. -/
def H2m : Prop :=
  ∀ c ∈ C, R.j ∪ R.m ⊆ c → ¬ R.i ⊆ c → R.l ⊆ c

/-- **H3**: some codeword contains k, l. -/
def H3 : Prop :=
  ∃ c ∈ C, R.k ∪ R.l ⊆ c

/-- **H4**: no codeword contains k, l, m. -/
def H4 : Prop :=
  ∀ c ∈ C, ¬ R.k ∪ R.l ∪ R.m ⊆ c

/-- **H5′**: some codeword contains i, m, p and not j. -/
def H5' : Prop :=
  ∃ c ∈ C, R.i ∪ R.m ∪ R.p ⊆ c ∧ ¬ R.j ⊆ c

/-- **H6**: some codeword contains j, m, p. -/
def H6 : Prop :=
  ∃ c ∈ C, R.j ∪ R.m ∪ R.p ⊆ c

/-- **H7**: some codeword contains i, j, m. -/
def H7 : Prop :=
  ∃ c ∈ C, R.i ∪ R.j ∪ R.m ⊆ c

/-- **F_A**: no codeword contains i, j, k, m, p. -/
def FA : Prop :=
  ∀ c ∈ C, ¬ R.i ∪ R.j ∪ R.k ∪ R.m ∪ R.p ⊆ c

/-- **F_B**: no codeword contains i, j, k, l, m. (Used only in Theorem 1(a).) -/
def FB : Prop :=
  ∀ c ∈ C, ¬ R.i ∪ R.j ∪ R.k ∪ R.l ∪ R.m ⊆ c

/-- The shared core of Theorem 1: H1ₘ, H2ₘ, H5′, H6, H7, F_A. -/
structure Core : Prop where
  h1m : H1m C R
  h2m : H2m C R
  h5' : H5' C R
  h6 : H6 C R
  h7 : H7 C R
  fA : FA C R

/-! Decidability, so the census can be checked by `decide`. -/

instance : Decidable (H1m C R) := by unfold H1m; infer_instance
instance : Decidable (H2m C R) := by unfold H2m; infer_instance
instance : Decidable (H3 C R) := by unfold H3; infer_instance
instance : Decidable (H4 C R) := by unfold H4; infer_instance
instance : Decidable (H5' C R) := by unfold H5'; infer_instance
instance : Decidable (H6 C R) := by unfold H6; infer_instance
instance : Decidable (H7 C R) := by unfold H7; infer_instance
instance : Decidable (FA C R) := by unfold FA; infer_instance
instance : Decidable (FB C R) := by unfold FB; infer_instance

end Hypotheses

/-! ### The target statements

These are the statements to be proved in later stages. They are stated here,
next to the definitions, so a reader can check them against the paper. -/

/-- **Theorem 1(b) (Rim\*)**, paper §5: Let `σ_i ≠ ∅`. If `C` satisfies the core
hypotheses (H1ₘ, H2ₘ, H5′, H6, H7, F_A) together with H3 and H4, then `C` is neither
open-convex nor closed-convex. (The closed half follows from Theorem 1(a), since H4 implies
F_B.) -/
def Theorem1b : Prop :=
  ∀ (n : ℕ) (C : Finset (Finset (Fin n))) (R : Roles n),
    R.i.Nonempty → Core C R → H3 C R → H4 C R → ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C

/-- **Theorem 1(a) (closed Rim)**, paper §5: Let `σ_i ≠ ∅`. If `C` satisfies the core
hypotheses together with F_B, then `C` is not closed-convex. (`σ_m = ∅` allowed.) -/
def Theorem1a : Prop :=
  ∀ (n : ℕ) (C : Finset (Finset (Fin n))) (R : Roles n),
    R.i.Nonempty → Core C R → FB C R → ¬ IsClosedConvex C

end RimRule
