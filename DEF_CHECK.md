# DEF_CHECK: Lean definitions vs the published papers

Referee pass, 2026-11-22. Checked commit `2b684fa` (working tree identical to HEAD; `Check.lean` is the only untracked file). No project file was edited.

**Result in one paragraph.** No mismatch that breaks the claim. The convexity definitions match the papers exactly, all 70 codes match WheelsCode codeword for codeword, the build passes, and every theorem depends only on `[propext, Classical.choice, Quot.sound]`. The one substantive finding: "locally good" rests on **two** cited facts, not one (finding F1). The rest are docstring and wording nits (F2 to F8).

## Sources read

| Source | How |
|---|---|
| Gambacini, Jeffs, Macdonald, Shiu, arXiv 1912.00963v3 | PDF downloaded, `pdftotext`. Def 2.1, 2.3, 2.4, Remark 2.5, Def 2.10, 2.13, 2.14, 2.15, Thm 3.11, Conj 3.13 |
| Chan, Johnston, Lent, Ruys de Perez, Shiu, arXiv 2011.04565v4 | PDF downloaded. Def 2.1, 2.3, 2.4, Assumption 2.5 |
| Curto et al., arXiv 1508.00150v4 | PDF downloaded. §1.2 (Δ(C), link, F∩), Def 3.5, Thm 1.3, Lemma 1.4, Lemma 4.5, Cor 4.6, Prop 4.8 |
| Council note `2026-11-20 Rim Theorem Upgrade part 2 (part 2).md` §5 | read from the vault |
| `Theorem 1 Referee Report.md` | read from the vault |
| github.com/aruysdeperez/WheelsCode, commit `46060723` | cloned; `Results/{Five,Six,Seven}Fac_WIRE_WHEEL_6.sage` parsed |

## Findings (ordered by importance)

**F1. Two cited facts, not one.** `all70_spec` proves `LinksCollapsible C`. To get "locally good" (1912.00963 Def 2.15) you need:
1. collapsible ⇒ contractible (textbook), and
2. Curto et al. Cor 4.6 / Lemma 1.4: a nonempty face that is not an intersection of facets has a cone link, so it is contractible.

Fact 2 is what lets `LinksCollapsible` skip the other missing faces. `Complex.lean` lines 41 to 43 do mention it, but the phrase "apart from the cited fact collapsible ⇒ contractible" undercounts. Also, "locally good" is never stated in Lean, so the step from `LinksCollapsible` to Def 2.15 is on paper only.
- Fix if you want one cited fact: extend the certificates to every nonempty face of Δ(C) ∖ C. There are 1,410 such faces across the 70 codes (278 covered now + 1,132 skipped). I checked in Python that all 1,132 skipped links are cones, so each collapses.

**F2. `inter` convention differs from the papers (harmless).** `Defs.lean:56` says "`U_∅ = ℝ^d` (here `univ`, automatically)". Chan Def 2.3: "By convention, the empty intersection is ∩_{i∈∅} U_i := X" (Gambacini Def 2.3 says the same). With a general X, `univ ≠ X`. It doesn't matter, because the realized code is defined by `codeOf X U = codeword U '' X` (`Defs.lean:61-62`), not through `inter`. It matches your note ("U_∅ = ℝ^d").

**F3. Citation label.** `Defs.lean:41-42` attributes the realization definition to "Chan et al. Def 2.4". The realized code is Chan Def 2.3(ii), stated with atoms, not with c(x); Def 2.4 is open/closed-convexity. The c(x) form is equivalent (shown below), but neither paper writes it that way.

**F4. "Paper" means your note, not the published papers.** `Defs.lean:32` quotes 'A neural code is C ⊆ 2^[n] with ∅ ∈ C'. Gambacini Def 2.1 and Chan Def 2.1 do not require ∅ ∈ C (Chan adds it as Assumption 2.5). No effect: `Theorem1a/1b` don't assume ∅ ∈ C, and all 70 codes contain ∅ (checked in Python; not stated in `all70_spec`, not needed).

**F5. `Theorem1b` is weaker than the note's 1(b).** Note §5: "(b) ... then C is neither open-convex nor closed-convex." `Defs.lean:175-177` concludes only `¬ IsOpenConvex C`. Harmless: H4 ⇒ F_B, so 1(a) gives the closed half, and `Rim70/Basic.lean` applies `theorem1a` separately with its own roles.

**F6. `all70` is a `List`.** `length_all70` shows 70 entries, but nothing in Lean says they are distinct or non-isomorphic. I checked in Python: 70 distinct codes, 70 isomorphism classes under relabeling of neurons 1..6. If the write-up says "70 codes up to relabeling", that part is outside Lean.

**F7. Header wording.** `Rim70/Data.lean:10-13` reads as if the filter (solved = 0, wheel = 0, reduced = 1, indecomposable = 1) yields these 70. The filter yields 1,800 codes (96 + 535 + 1,169). The 70 are the ones where role assignments for both halves were found. `data/rim70.json` says "780 faces"; there are 278 distinct faces (PROGRESS.md already explains this).

**F8. Not proved in Lean, not needed:** that the 7-neuron code with neuron 0 silent is equivalent to the 6-neuron code (item 3).

## Item 1: `RimRule/Defs.lean`

| Object | Lean lines | Source | Verdict |
|---|---|---|---|
| neural code | 33-34 | note §5; Chan Assumption 2.5 | MATCH with the note; see F4 |
| c(x) | 52-54 | note §5 | MATCH |
| U_σ | 57-58 | note §5; papers use U_∅ := X | MATCH with the note; see F2 |
| code(U, X) | 61-62 | Gambacini Def 2.3, Chan Def 2.3 | MATCH (equivalent form) |
| realization | 65-68 | Gambacini Def 2.4(1)(2), Chan Def 2.4(ii) | MATCH |
| basic fact | 71-74 | note §5 | MATCH (Lean proves it for every x, not only x ∈ X) |
| open-convex | 83-85 | Gambacini Def 2.4, Chan Def 2.4 | MATCH |
| closed-convex | 88-90 | same | MATCH |
| roles | 96-102 | note §5 | MATCH |
| H1ₘ, H2ₘ | 109-114 | note §5 | MATCH |
| H3, H4 | 117-122 | note §5 | MATCH |
| H5′, H6, H7 | 125-134 | note §5 | MATCH |
| F_A, F_B | 137-142 | note §5 | MATCH |
| Theorem1a | 181-183 | note §5 (a) | MATCH |
| Theorem1b | 175-177 | note §5 (b) | MATCH for the open half; weaker than the note, see F5 |

Details behind the MATCH verdicts:
- **code(U, X).** The papers define σ ∈ code(U, X) ⇔ U_σ ∖ ⋃_{j∉σ} U_j ≠ ∅ with U_∅ := X. A point x lies in that atom exactly when x ∈ X and c(x) = σ (for σ ≠ ∅, x ∈ X follows from U_i ⊆ X). So the atom definition equals `codeword U '' X` whenever `U s ⊆ X`, which `IsRealization.subset` requires.
- **Stimulus space.** Lean allows any X ⊇ ⋃ U_s, as Def 2.4 does. Gambacini Remark 2.5 then fixes X = ℝ^d. Lean's `¬ IsOpenConvex` rules out every X, so it covers both readings. Direction: Lean's negation is at least as strong as the paper's. That is the safe direction.
- **Open / closed / convex.** `IsOpen`, `IsClosed`, `Convex ℝ` on `Fin d → ℝ` (product topology = the usual one). Open means open in ℝ^d, not relative to X, as in the papers. d = 0 is allowed, which only strengthens the negation.
- **"Not j".** `¬ R.j ⊆ c` means "does not contain all of σ_j", which is what the proof uses (points outside U_j = ⋂_{s∈σ_j} U_s). Not "disjoint from σ_j".
- **σ_i ≠ ∅** is `R.i.Nonempty`. σ_m = ∅ is allowed in both statements; for 1(b) it makes H3 and H4 contradict, so that case is empty.
- **Referee fixes.** Fixes 1 to 7 concern the proof text, Lemma 1, Prop 2 and the sharpness tables; none changes the statement. Fix 8 (drop σ_i ≠ ∅) is optional and not taken. The statements in `Defs.lean` are the fixed statements.
- **Positive control (mine, not in the project).** I proved in a scratch file that {∅, {0}} on one neuron satisfies both `IsOpenConvex` and `IsClosedConvex`. So the definitions aren't accidentally unsatisfiable.

## Item 2: `RimRule/Complex.lean`

| Object | Lean lines | Source | Verdict |
|---|---|---|---|
| maximal codewords | 59-60 | Gambacini Def 2.1 | MATCH |
| Δ(C) | 64-65 | Gambacini Def 2.10, Curto §1.2 | MATCH |
| link | 106-107 | Curto §1.2, Gambacini Def 2.13 | MATCH (literal) |
| free face | 113-114 | standard | MATCH |
| elementary collapse | 121-123 | standard | MATCH |
| Collapsible | 142-144 | standard (collapses to a point) | MATCH |
| IsMaxInter | 150-151 | Curto F∩(Δ) | MATCH |
| LinksCollapsible | 156-158 | see below | MATCH as a combinatorial statement |
| hull_eq_of_isMaxInter | 195-206 | Curto: σ = f_σ ⇔ σ is an intersection of facets | MATCH |

**Does `LinksCollapsible` + the cited chain give "locally good" (Def 2.15)?** Yes.
- Def 2.14/2.15: C is locally good iff every nonempty σ ∈ Δ(C) with non-contractible Lk_σ(Δ(C)) is in C. So it's enough that every nonempty σ ∈ Δ(C) ∖ C has a contractible link.
- If σ is an intersection of maximal codewords: `IsMaxInter` holds (it is literally the definition of F∩ with a nonempty family), `LinksCollapsible` gives a collapsible link, and cited fact 1 gives contractible.
- If not: Curto Cor 4.6 gives a cone link, hence contractible. In its words, a non-contractible link means "σ must be an intersection of facets of ∆".
- **The skip is justified by a cited result:** Curto Lemma 1.4 / Cor 4.6. Gambacini et al. use the same reduction in the proof of their Theorem 3.11 (citing Curto Thm 1.3 and Lemma 1.4).

Other things I checked here:
- **Collapse soundness.** The free-face condition makes τ a maximal face and the unique proper coface of σ, so removing the pair keeps a simplicial complex. `IsFreeFace` doesn't exclude σ = ∅, but a sequence that removes ∅ can never end at `{∅, {v}}`, so no valid certificate uses it.
- **The complex being collapsed is the right one.** `link_delta_eq` (177-185) proves `linkDelta C σ = link (delta C) σ`, and `isComplex_delta` shows Δ(C) is a complex.
- **Coverage.** `CertCovers` (211-212) quantifies over every nonempty non-codeword face with `hull C σ = σ`, which is exactly Curto's σ = f_σ.
- **Facets.** A facet has empty link (non-contractible), so facets are mandatory. They are codewords, and `LinksCollapsible` only asks about σ ∉ C. Consistent.
- See F1 for the count of cited facts.

## Item 3: neuron labels (`Fin 7`, neuron 0 unused)

**MATCH; no effect.**
- **Convexity.** In any realization, no codeword contains 0, so U₀ ∩ X = ∅; with U₀ ⊆ X this forces U₀ = ∅. The empty set is open, closed and convex. So the 7-neuron code is open-convex (closed-convex) iff the 6-neuron code is. Not proved in Lean (F8).
- **Local goodness.** Vertex 0 is in no face of Δ(C), so Δ(C) and every link are the same set families.
- **Conjecture 3.13** covers codes "on at most 7 neurons". A code in 2^[7] with one silent neuron is a code on 7 neurons by Def 2.1, so `all70_spec` applies to the conjecture directly with n = 7, without the 6-neuron equivalence. You need the one-line argument above only if the write-up says "6 neurons".
- **Fin literal wraparound.** A numeral ≥ 7 in `Fin 7` would wrap silently. I checked: every codeword, role and certificate entry uses only 1..6.

## Item 4: `Census.lean` and `Rim70/Data.lean` vs WheelsCode

**MATCH, all 70 (not only 10).** Parsed `Data.lean` and the three `.sage` files and compared by id.
- Every Lean code equals the source `'C'` list as a set of codewords. No duplicates on either side.
- Every one of the 70 has source flags solved = 0, wheel = 0, reduced = 1, indecomposable = 1, and its `'sc'` facets equal the maximal codewords of the Lean code.
- Every docstring count ("N codewords, M maximal") is right, and FiveFac/SixFac/SevenFac ids have 5/6/7 facets.
- `Census.C033` = `Data.FiveFac399` = source FiveFac399 (13 codewords). `data/C5-033.md` cites the secondary repo `NotItsMe/neural-codes-96`; it agrees with the primary source.

Twelve of them, listed:

| id | codewords (source / Lean) | facets | equal |
|---|---|---|---|
| FiveFac399 | 13 / 13 | 5 | yes |
| FiveFac639 | 14 / 14 | 5 | yes |
| FiveFac681 | 14 / 14 | 5 | yes |
| SixFac935 | 19 / 19 | 6 | yes |
| SixFac1358 | 19 / 19 | 6 | yes |
| SixFac1573 | 20 / 20 | 6 | yes |
| SevenFac1454 | 24 / 24 | 7 | yes |
| SevenFac1970 | 25 / 25 | 7 | yes |
| SevenFac2288 | 26 / 26 | 7 | yes |
| SevenFac2437 | 25 / 25 | 7 | yes |
| SevenFac2530 | 27 / 27 | 7 | yes |
| SevenFac2575 | 25 / 25 | 7 | yes |

Independent re-check in Python (my own code, not `gen_rim70.py`), all 70 codes:
- Hypotheses of 1(b) with `openRoles` and of 1(a) with `closedRoles`: all hold.
- Faces that need a certificate (nonempty, not a codeword, equal to their hull): 278. The Lean certificates list exactly these, no extra and none missing.
- All 278 collapse sequences are valid and end at the stated vertex. All 278 links also have zero reduced homology over GF(2), GF(3) and GF(1000003).
- The 1,132 skipped missing faces all have cone links.

## Item 5: `Rim70/Summary.lean`

**MATCH.** Lines 38-39:

```lean
theorem all70_spec :
    ∀ C ∈ all70, ¬ IsOpenConvex C ∧ ¬ IsClosedConvex C ∧ LinksCollapsible C
```

- `all70` (23-33) has 70 entries, the same 70 names as `Data.lean`, each once. The 70 `exact` lines use the matching code's own `not_convex` and `linksCollapsible`.
- It states exactly the three properties and nothing else. It does not state: ∅ ∈ C, distinctness (F6), or "locally good" (F1).

## Item 6: forbidden constructs, build, axioms

**MATCH.**
- `grep -w` over every `.lean` file for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern` (and `ofReduceBool`, `opaque`, `partial`, `csimp`, `macro`, `elab`): no hits in code. The only hit is the phrase "no `native_decide`" in a comment at `Census.lean:12`.
- The only `set_option` is `linter.style.header false`. Computation uses `decide +kernel` (137 uses), which adds no axiom.
- **Build.** Your PC's Lean isn't reachable from my shell (the bridge gives me a Linux sandbox with no Lean, and I didn't want to touch your `.lake`). So I copied the source files at `2b684fa` into a clean Linux workspace: Lean 4.36.0, mathlib `fc4f59e` from your `lake-manifest.json`, mathlib cache, then `lake build`. Result: `Build completed successfully (3420 jobs)`. Only warnings: "consider adding `module`".
- **`lake env lean Check.lean` output:**

```
RimRule.Rim70.all70_spec : ∀ C ∈ RimRule.Rim70.all70,
  ¬RimRule.IsOpenConvex C ∧ ¬RimRule.IsClosedConvex C ∧ RimRule.LinksCollapsible C
'RimRule.Rim70.all70_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RimRule.C033_not_isOpenConvex' depends on axioms: [propext, Classical.choice, Quot.sound]
'RimRule.C033_not_isClosedConvex' depends on axioms: [propext, Classical.choice, Quot.sound]
'RimRule.theorem1b' depends on axioms: [propext, Classical.choice, Quot.sound]
'RimRule.theorem1a' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Same three axioms for `linksCollapsible_of_certOK`, `hull_eq_of_isMaxInter`, `link_delta_eq` and `not_convex_of_hyps`.

## Not checked

- **Whether Conjecture 3.13 is still open.** Two web searches found no earlier counterexample on 7 or fewer neurons. That is not a literature review. Ask Shiu or Jeffs, or search properly, before claiming novelty.
- **Whether 70 is the full count.** I didn't test the other 1,730 filtered WheelsCode codes against Theorem 1.
- **The proofs' informal text.** Lean checks the proofs; I compared statements and definitions, not the prose in the note line by line.
- **The build on your Windows machine.** Run `lake env lean Check.lean` there once to confirm the same output.

## Verdict

Yes: Lean proves, with standard axioms only, that each of the 70 codes (as a code on 7 neurons) is neither open-convex nor closed-convex in the sense of Def 2.4 and has `LinksCollapsible`; that makes them counterexamples to Conjecture 3.13 given **two** cited facts rather than one, namely collapsible ⇒ contractible and Curto et al. Cor 4.6 / Lemma 1.4 (the faces `LinksCollapsible` skips have contractible links).
