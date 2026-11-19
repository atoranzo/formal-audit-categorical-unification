# Version 1.2: changes from version 1.1

*A Formal Audit of a Categorical Unification of Consciousness Theories: Structural Proxies,
Formal Obstructions and a Positive Route*, preprint and verification archive, version 1.2,
19 November 2026. Not peer reviewed.

Version 1.1 is deposited on Zenodo with the DOI
[10.5281/zenodo.24361411](https://doi.org/10.5281/zenodo.24361411) (GitHub tag `v1.1`) and is
not modified. Version 1.2 receives its own DOI when it is released; until then the concept DOI
[10.5281/zenodo.24349943](https://doi.org/10.5281/zenodo.24349943), which resolves to the latest
version, is used wherever a DOI for the current version is needed.

Q is neither demonstrated nor refuted, in version 1.2 as in versions 1.0 and 1.1. Version 1.2
corrects eighteen imprecisions of version 1.1 (errata 1–18 below: eight minor, ten nits) and makes
six improvements (I1–I6). No proved statement, figure or numerical value changes, and no numbered
result is added. Items 9 and 12 change the caption of Table 4 and the row (R7) of Table 1 so that their
labels state the scope that the text already gave; the other errata correct wording. Items marked †
were false as printed; for items 3, 6 and 15, only in a degenerate case or in a comment that states
no result. Improvement I1 certifies exactly the decrease of J in Remark 53, which version 1.1
labelled [N], and changes its label to [S]; I2 adds a comparison computed exactly [S], and I3
statements checked in Lean with Mathlib [M]. Each is checked by a new script or by new theorems of
the archive.

The corrections and improvements come from an adversarial verification, by agents of the same AI
assistant (Claude Code, by Anthropic), of a reading of version 1.1 that the author made in
conversations with Claude (Anthropic) outside Claude Code; that reading was treated as unverified
input, and the assistant applied the corrections and improvements, at the request and under the
direction of the author, with no independent human review. The declaration on the use of generative
AI in the paper says so.

Results, sections, tables and equations keep the numbers of version 1.1, and the changes below
cite them by those numbers. Locations give the file in `paper/source/` and its line, which is the
same in versions 1.1 and 1.2, and the page of the PDF of version 1.1.

## Errata 1–18

1. **Section 6.4, item 4, "Check the digraph"** (minor †; `en/G_positive_route.tex` l. 84,
   p. 47). Version 1.1 said that the comparison is informative exactly outside the strongly
   connected components of the intervention digraph and that within a component u is forced to
   be constant. It omitted the premises u = f∘κ and IM_𝒯 for u, which the Scope of Theorem 51,
   item (ii), declares unjustified; read literally, "outside the strongly connected components" is
   empty, since every class lies in some component; "exactly" denied that a strict difference
   within a component is informative, although it would contradict the premises; and the freedom
   of comparisons is only pairwise. The item now states the premises, says that u then takes one
   value on the realizations whose classes lie in one component and does not decrease along the
   paths of the digraph, and that a single comparison of two realizations can show a variation of
   u only when their classes lie in different components and can contradict the premises only when
   one class is reachable from the other. A final sentence adds that such a contradiction refutes
   the conjunction of these premises with the declared digraph and the measurement of u, and does
   not show which of them fails.
2. **Three sentences without "of the form f∘κ"** (minor †). Without it each sentence was false:
   u = Φ_Q satisfies IM_𝒯 and is not constant on a strongly connected component. The restriction
   to degrees of the form f∘κ is added in the abstract (`main.tex` l. 11, p. 1), in the item
   "Act III" of the introduction (`en/0_introduction.tex` l. 12, p. 3, which now also says "on the
   realizations of each strongly connected component" and "such degrees exist") and in item (R7)
   of Section 1.1 (`en/0_introduction.tex` l. 24, p. 4). The copies of the sentence in the archive
   are corrected too: the description in `.zenodo.json`, the description and the short abstract
   in `metadata/zenodo_metadata.md`, and the summary of the third act in `README.md`.
3. **Formal check of Theorem 51(b)** (nit †; `en/G_positive_route.tex` l. 29, p. 44). "Its proof
   uses only transitivity and antisymmetry, not reflexivity" referred to the proof of
   `constant_on_scc`, which uses reflexivity (`le_refl`), as does the paper proof (paths of
   length 0); only the separate proof `b_transitive_antisymmetric` avoids it. The text now says
   "a separate proof uses only transitivity and antisymmetry, not reflexivity", and so does the
   same item in Section 5 of the changes of version 1.1 below.
4. **(G7), the derivative of r** (minor †; `en/E_gaussian.tex` l. 86, p. 38). Version 1.1 wrote
   ∂r/∂p = k(k+1)/(kp+1)² > 0, but F_mem admits k = 0, where ∂r/∂p = 0 and r ≡ 1. The text now
   says that the derivative is positive for k > 0 and that r ≡ 1 for k = 0.
5. **(G3), "indexed by |z|"** (minor; `en/E_gaussian.tex` l. 55, p. 36). |z| is invariant but not
   complete. The text now gives the classification for all isomorphisms: pointed states in a fibre
   of J are classified by z up to sign if c > 0 and by (|z_1|, |z_2|) if c = 0, and histories by
   z_{0:T} up to the same identifications; |z| alone already separates a continuum of classes.
6. **Section 4.6, "only the minimum-cut bound holds"** (nit †; `en/D_weak_unification.tex` l. 99,
   p. 32). On the band the upper bound of the sandwich also holds; what fails there is the hub
   bound. The sentence now says that on the band the hub bound of Theorem 37(d) gives nothing and
   that the only positive lower bound is the minimum-cut bound.
7. **Section 6.4, item 1** (minor; `en/G_positive_route.tex` l. 81, p. 47). It listed four exits,
   whereas the abstract and Section 1 list five; "equating only isomorphic realizations" is added.
   The short abstract in `metadata/zenodo_metadata.md`, which had the same four exits, now lists
   the fifth as well.
8. **Section 3.2, "the demanding reading"** (minor; `en/C_categorical.tex` l. 32, p. 24). The
   singular followed a sentence that names two demanding readings, and under the reading in which
   a hub must send to every other unit the driver of F_0 is a hub (Section 5). The sentence now
   distinguishes them: requiring coupling in both directions, the two-unit family has no hub
   (`f0_hub_readings`) and lies in the band at n = 2; requiring a hub to send to every other unit,
   its driver is a hub, but the directed path on three units has none (Section 1.1, Limitations).
9. **Caption of Table 4** (nit; `en/C_categorical.tex` l. 114, p. 28). "Numerical upper bounds,
   [N]" also covered the value 0 of 2K_2, which is exact. The caption now gives [N] for C_4,
   K_{1,3} and P_4, says that the value 0 of 2K_2 is exact, and that all signs are given by
   Lemma 29.
10. **Remark 53, the decrease is local** (nit, exposition; `en/G_positive_route.tex` l. 67,
    pp. 46–47). The remark paired the indefiniteness of S with the decrease of J. A sentence is
    added before the last one: the decrease is local, J(A(c)) increases again for larger c, and S
    is indefinite on a wider range of c than the decrease, so the indefiniteness of S does not by
    itself make J decrease [N]. A new script, `python/numeric/barrido_diagonal_fija.py`, checks it
    on a grid of c from 0.005 to 0.600 with step 0.005: J decreases only from c = 0.340 to
    c = 0.380 and increases on every other step, and S is indefinite (det S < 0, exact) from
    c = 0.005 to c = 0.395; Table 10 (`en/F_appendices.tex` l. 74) and Table 14
    (`en/Z_files_axioms.tex` l. 31) cite it.
11. **Section 6.5, item (ii)** (minor; `en/G_positive_route.tex` l. 90, p. 48). The digraph needs
    Φ_Q and κ, which are defined on D_0, and item (iii) of the Scope of Theorem 51 refers to this
    item; read literally, a bench instance with J would have seemed to address it. The item now asks
    for a physically specified class 𝒯 of interventions on bearers of D_0, such as deformations of
    the couplings of the systems of Open_G that represent them at grain γ, with the original
    descriptor Φ_Q, and for the strongly connected components of its intervention digraph on the
    realized coexperience classes.
12. **Table 1, row (R7) on the two collapses** (minor; `en/0_introduction.tex` l. 70, p. 7). The
    label [L] was given without its scope: `exact_covariance_gives_Su` covers directed chains
    only, and `order_all_pairs_collapse` is the instance with two levels and two classes. The row
    now gives [L] for the pairwise and two-level forms and [A] for the general product case, cites
    `exact_covariance_components` and `order_all_pairs_general` (integer values), and says that
    the general product case follows from `order_all_pairs_general` by a one-line paper argument.
    Section 6.1 and Table 11 already stated this scope.
13. **Section 6.1, "The order clause B on all pairs"** (nit; `en/G_positive_route.tex` l. 7,
    p. 43). What is a product is the joint image of (Φ_Q, κ), the term defined in Section 2.5, not
    the image of κ. The sentence now says "such that (Φ_Q, κ) has product image and Φ_Q takes at
    least two distinct values".
14. **Scope of Theorem 51, item (ii)** (nit; `en/G_positive_route.tex` l. 35, p. 45). "…for
    u_orig, which the order clause B implies…" could be read as if B also implied u_orig = f∘κ.
    The four premises are now separated by semicolons, and the clause on B attaches to IM_𝒯 alone.
15. **Section 6.3, "What IM_𝒯 would then predict"** (nit †; `en/G_positive_route.tex` l. 76,
    p. 47). With a single realized class the one-vertex digraph is strongly connected and nothing
    recurs. The sentence now begins "With at least two realized classes".
16. **Discussion after Proposition 50** (nit; `en/E_gaussian.tex` l. 149, p. 40). That the history
    determines the law needs only pairwise disjoint supports; the injectivity of F is needed only
    for the second consequence. The two consequences are now separated.
17. **Notation overloads** (nit). A notice is added where a letter had a second meaning without
    one: in Definition 4(a), the set E of aspects is unrelated to the noise covariance E of Open_G
    (`en/A_obligation.tex` l. 47, p. 10); in Theorem 36, κ_E is a condition number, unrelated to
    the map κ of Sections 2 and 6 (`en/D_weak_unification.tex` l. 18, p. 29); in Theorem 51, the
    function f on the classes is unrelated to the correspondences f of Definition 4(c)
    (`en/G_positive_route.tex` l. 18, p. 44).
18. **Section 2.7, "Refuting SEG would require three things"** (nit; `en/B_principles_best.tex`
    l. 50 and l. 56, p. 20). The list describes refutation through a counterexample to S_u, and
    now says so. A sentence is added after the list: by Proposition 25(b), SEG also fails if
    u = ψ∘𝔘 is constant on D_0, and that would not refute S_u. Table 13 (`en/F_appendices.tex`
    l. 148, p. 56), which repeats the list, now also says "through a counterexample to S_u".

## Improvements

- **I1. Remark 53: the decrease of J is certified exactly** (`en/G_positive_route.tex` l. 67,
  pp. 46–47). Version 1.1 labelled the decrease J(A(0.33)) > J(A(0.38)) [N]: its script takes the
  minimum over the real critical points of the residual determinant, found by 50-digit root
  finding, and that this finds all of them was not certified. A new script,
  `python/exact/certificado_diagonal_fija.py`, certifies the decrease [S]: for fixed y the residual
  determinant is a quadratic in x with leading coefficient at least P₁₁E₂₂ > 0, so its minimum
  over x is explicit; the minimum over y lies at a real zero of a polynomial of degree 5 that has
  exactly one real zero (Sturm sequences), isolated exactly; and exact rational interval
  arithmetic encloses each value of J in an interval of width below 10⁻⁴⁰, giving
  J(A(0.33)) = 0.1040827049… > J(A(0.38)) = 0.0997015975…. The remark still says that no paper
  proof implies the decrease, and now says that it rests on the exact certificate. The label of
  the decrease changes from [N] to [S] in row (R7) of Table 1 (`en/0_introduction.tex` l. 73) and
  in Table 10 (`en/F_appendices.tex` l. 74), which also names the new script; the abstract
  (`main.tex` l. 11) no longer says "numerically"; the introduction says that the decrease is
  shown with an exact certificate (`en/0_introduction.tex` l. 12) and labels it [S] (l. 24). The
  copies in `README.md`, `.zenodo.json` and `metadata/zenodo_metadata.md` follow, and the item on
  this decrease is removed from the list of what remains open in the section on version 1.1
  below. The remark names the script of the certificate after "certified exactly".
- **I2. Section 5.4: J(C₄) > J(P₄), exactly** (`en/E2_networks.tex` l. 27, p. 42). Version 1.1 did
  not state this comparison. An item is added after the one on the band: on P₄ the predictor
  B = A − A_cross({0}|{1,2,3}) of the proof of Theorem 36 gives
  det(E + (A − B) P (A − B)ᵀ)/det E = det(I + A_cross P A_crossᵀ) = 637088/511841 < 34/25, so
  J(P₄) ≤ ½ log(637088/511841) ≈ 0.109447 < ½ log(34/25) ≈ 0.153742 ≤ J(C₄) [S] (with
  Theorem 36). A new script, `python/exact/anillo_frente_camino.py`, computes it in rational
  arithmetic; Table 11 (`en/F_appendices.tex` l. 101) lists it with the four-unit networks.
- **I3. Theorem 51: which order hypotheses are necessary** (`en/G_positive_route.tex` l. 29,
  p. 45). A sentence is added after "no minimality is claimed beyond them": antisymmetry is
  necessary for (b) to hold in every digraph, and transitivity is not; (b) holds in every digraph
  exactly when no cycle of ≤ passes through two distinct values
  (`QAuditFrontier.b_iff_closure_antisymm`), as for the reflexive and antisymmetric but not
  transitive relation of `QAuditFrontier.b_holds_succ3`; and the hypotheses of
  `QAuditFrontier.c_ne_of_two_values` are also necessary for (c) in its ≠ form to hold in every
  digraph, loops included (`QAuditFrontier.c_ne_iff_two_values`) [M]. Earlier in the paragraph,
  "neither can be dropped" now reads "neither can simply be dropped": each hypothesis has a
  counterexample when it is removed, but only antisymmetry is necessary. The clause before the
  new sentence, "no minimality is claimed beyond them", now reads "beyond them, no minimality is
  claimed except what the next sentence states". Seven theorems are added to
  `lean-mathlib/QAuditAnalytic/FrontierReal.lean`, in the namespace `QAuditFrontier`:
  `chain_map`, `b_iff_closure_antisymm`, `antisymm_of_closure_antisymm`, `succ3_props`,
  `succ3_chain_val`, `b_holds_succ3` and `c_ne_iff_two_values`, with two definitions and an
  instance that they use (`succ3`, `Eloop2` and `DecidableRel succ3`); they were first compiled in
  the adversarial verification, against the file of version 1.1. Appendix B
  (`en/Z_files_axioms.tex` l. 24, l. 44 and l. 52) and the expected output of the module list the
  theorems with their axioms.
- **I4. Section 6.1, "The order clause B on all pairs"** (`en/G_positive_route.tex` l. 7, p. 43).
  A sentence is added at the end of the paragraph: the product condition is sufficient, not
  necessary; by Theorem 51 with 𝒯 = D_0 × D_0, B on all pairs forces f to be constant on im κ
  exactly when the digraph "k occurs strictly below k′" on im κ is strongly connected.
- **I5. Definition 1(d)** (`en/A_obligation.tex` l. 13, p. 8). Measurability is made explicit for
  continuous state sets: the X_i are standard Borel spaces, the r_i are Borel isomorphisms, and
  the kernel of unit β(i) at r(z) is the image of the kernel of unit i at z under r_i.
- **I6. The DOI of version 1.1**, 10.5281/zenodo.24361411, assigned on release, is cited in the
  note on the title page of the paper (`main.tex` l. 7), in `README.md`, `CITATION.cff`,
  `.zenodo.json` and `metadata/zenodo_metadata.md`, and in the section on version 1.1 below, where
  it was said to be assigned on release; the item "The DOI of version 1.1 is assigned when it is
  released" is removed from its list of what remains open.

## Version, provenance and metadata

- Note on the title page (`main.tex` l. 7): version 1.2, 19 November 2026; the changes from
  versions 1.0 and 1.1 are listed in this file; the DOI of version 1.1 (I6).
- Declaration on the use of generative AI (`main.tex` l. 30): a sentence on where the changes of
  version 1.2 come from and who applied them (the paragraph above). The same sentence is added to
  the copies of the declaration in `README.md`, `.zenodo.json` and `metadata/zenodo_metadata.md`.
- The same declaration and its copies now name the AI system that versions 1.0 and 1.1 called
  "another AI system": the author states that it was Claude (Anthropic), used outside Claude
  Code, both for the reading of version 1.1 behind these changes and in the exploratory
  conversations during the research, and that no AI system other than Anthropic's Claude was used.
- `README.md`, `CITATION.cff`, `.zenodo.json`, `metadata/zenodo_metadata.md` and `LICENSE`:
  version 1.2, of 19 November 2026; the name of the archive to upload by hand is
  `formal-audit-categorical-unification-v1.2.zip`; the note of `README.md` on the numbers of
  results and tables also names version 1.2. `.zenodo.json` and `metadata/zenodo_metadata.md`
  record version 1.1 as the previous version (relation "is new version of", DOI
  10.5281/zenodo.24361411). The DOI of version 1.2 is assigned by Zenodo on release; none is given
  in the archive.
- The short abstract of `metadata/zenodo_metadata.md` (item 2) keeps within 1920 characters: it
  says that intervention monotonicity escapes the collapse, "forcing degrees f∘κ to be constant
  exactly on the strongly connected components of an intervention digraph", and it gives the
  number of archived scripts in figures, 15; it lists the five exits (item 7). To make room, five
  phrases are shortened without change of meaning ("The author's candidate theory Q", "by different
  invariants", "not the theories themselves", "Q's unity-sufficiency obligation S_u", "a stand-in, not
  the descriptor of Q"); it has 1918 characters.

## Files of the archive

- Added: `python/exact/certificado_diagonal_fija.py` (I1), `python/exact/anillo_frente_camino.py`
  (I2) and `python/numeric/barrido_diagonal_fija.py` (erratum 10), with their expected outputs
  `python/expected/salida_certificado_diagonal_fija.txt`,
  `python/expected/salida_anillo_frente_camino.txt` and
  `python/expected/salida_barrido_diagonal_fija.txt`; `python/verify_python.sh` runs the first two
  as exact scripts and the third as a numerical one.
- Changed:
  - `paper/` (the LaTeX sources `main.tex`, `en/0_introduction.tex`, `en/A_obligation.tex`,
    `en/B_principles_best.tex`, `en/C_categorical.tex`, `en/D_weak_unification.tex`,
    `en/E2_networks.tex`, `en/E_gaussian.tex`, `en/F_appendices.tex`, `en/G_positive_route.tex`
    and `en/Z_files_axioms.tex`, and a PDF built from them); Table 14 has rows for the two new
    exact scripts (`en/Z_files_axioms.tex` l. 28 and l. 30) and lists the new numerical script in
    the row of the other monotonicity grids (l. 31); so that Tables 10 and 14 still fit on their
    pages, their column widths change (`en/F_appendices.tex` l. 65, `en/Z_files_axioms.tex` l. 7)
    and Table 14 has a column separation of 5 pt instead of 6 pt (l. 6);
  - `lean-mathlib/QAuditAnalytic/FrontierReal.lean`, with the seven theorems of I3, the two
    definitions and the instance that they use, and the `#print axioms` of the theorems, and its
    expected output, `lean-mathlib/expected/salida_FrontierReal.txt`;
  - `python/verify_python.sh` (the three new scripts), and the number of scripts in `Makefile` and
    `verify_all.sh`;
  - `README.md`, `CHANGES.md`, `CITATION.cff`, `.zenodo.json`, `metadata/zenodo_metadata.md`,
    `LICENSE` (version line) and `SHA256SUMS`.
- Counts: the archive has fifteen Python scripts (twelve in version 1.1), and the eight modules
  of the Lean project with Mathlib print 111 `#print axioms` reports (104 in version 1.1): 93
  list the three standard axioms, and the other eighteen, all in `FrontierReal.lean`, list no
  axioms (fourteen), `propext` alone (two) or `propext` and `Quot.sound` (two). The counts are
  updated wherever they are printed: the abstract and the section on the use of generative AI
  and verification (`main.tex` l. 11 and l. 32), the introduction (`en/0_introduction.tex` l. 12
  and l. 42), Appendices A and B (`en/F_appendices.tex` l. 2, `en/Z_files_axioms.tex` l. 44),
  `README.md`, `CITATION.cff`, `.zenodo.json`, `metadata/zenodo_metadata.md`, `Makefile` and
  `verify_all.sh`.
- Unchanged: the Lean files without Mathlib, the other seven modules of the Lean project with
  Mathlib and their expected outputs, the other twelve Python scripts and their expected outputs,
  `python/compare_outputs.py`, `lean/verify_lean.sh`, `lean-mathlib/verify_mathlib.sh`,
  `.gitignore`, `.gitattributes`, the class file and the other LaTeX sources.

# Changes from version 1.0 to version 1.1

*A Formal Audit of a Categorical Unification of Consciousness Theories: Structural Proxies,
Formal Obstructions and a Positive Route*, preprint and verification archive, version 1.1,
19 November 2026. Not peer reviewed.

Version 1.0 is deposited on Zenodo with the DOI
[10.5281/zenodo.24349944](https://doi.org/10.5281/zenodo.24349944) (GitHub tag `v1.0`) and is
not modified. Version 1.1 received its own DOI on release,
[10.5281/zenodo.24361411](https://doi.org/10.5281/zenodo.24361411); until then the concept DOI
[10.5281/zenodo.24349943](https://doi.org/10.5281/zenodo.24349943), which resolves to the latest
version, was used wherever a DOI for the current version was needed.

Q is neither demonstrated nor refuted, in version 1.1 as in version 1.0. No result added in
version 1.1 is a demonstration of Q or of any of its obligations: the new theorem of Section 2.8
is conditional and establishes none of its premises, and the real-valued form of Theorem 51 is a
statement about mathematical degrees, not about the unity degree of Q.

The pre-submission review that led to version 1.1 (its adversarial verification, the conditional
theorem of Section 2.8 and its Lean file, the Lean module with real-valued degrees for
Theorem 51 and the archived second check of Table 6) was done by agents of the same AI assistant
that drafted version 1.0 (Claude Code, by Anthropic), at the request and under the direction of
the author, with no independent human review. The declaration on the use of generative AI in the
paper says so; it also says that the text of version 1.0 was translated from its Spanish master
version and that the changes of version 1.1 were written in English.

## Numbering

A new Theorem 26 (Section 2.8, also new) and a new Table 3 shift every later printed number by
one. Results are cited below by their numbers in version 1.1, with the number of version 1.0 in
parentheses where it differs.

| Label in the LaTeX source | Version 1.0 | Version 1.1 |
|---|---|---|
| `thm:conditional-discharge` (Section 2.8, `sec:conditional`) | — | Theorem 26 |
| `tab:kinds` | — | Table 3 |
| Definition 26 (finite open system with a blanket; no label) | 26 | 27 |
| `prop:funtor`, `lem:J`, `rem:small`, `prop:monoidal` | 27, 28, 29, 30 | 28, 29, 30, 31 |
| `thm:translation`, `thm:reconstruccion`, `thm:bridge`, `prop:decomposition` | 31, 32, 33, 34 | 32, 33, 34, 35 |
| `thm:cheeger`, `thm:laxa`, `thm:section`, `def:SEL` | 35, 36, 37, 38 | 36, 37, 38, 39 |
| `thm:unif`, `thm:locus`, `thm:collapse`, `thm:selection`, `prop:conditional` | 39, 40, 41, 42, 43 | 40, 41, 42, 43, 44 |
| `def:gauss-F0`, `def:gauss-Fmem`, `def:IPS`, `prop:windows`, `prop:gauss-chains`, `prop:gauss-plateau` | 44–49 | 45–50 |
| `thm:frontier`, `prop:scaling`, `rem:fixed-diagonal`, `cor:band-scaling` | 50, 51, 52, 53 | 51, 52, 53, 54 |
| `tab:C-1`, `tab:E-1`, `tab:networks` | Tables 3, 4, 5 | Tables 4, 5, 6 |
| `tab:corr-1` … `tab:corr-6`, `tab:F-3`, `tab:files` | Tables 6–11, 12, 13 | Tables 7–12, 13, 14 |

Every result numbered 26 or more in version 1.0 is one higher in version 1.1, and every table
numbered 3 or more as well. Numbers below 26, the sections, Figure 1, Tables 1 and 2 and the
equations keep their numbers.
The PDF of version 1.1 has 62 pages (version 1.0: 54).

## 1. Corrections of statements of version 1.0

1. **The second check of the four-unit networks was not independent.** Version 1.0 said, in the
   caption of Table 5 (now Table 6), that "a second, independent optimizer, which is not
   archived, reproduced J to seven digits", and its declaration on the use of generative AI said
   that this check was not part of the archive. The check was section (1) of a working script,
   `verif_gauss.py`. For each bipartition it kept the smaller of two values computed from the
   starting predictor B = A − A_cross(π): a BFGS value and the value of an alternating weighted
   least-squares scheme. It is not independent of `pistas_numerico.py`. It shares the objective,
   the system data and the starting predictor, and it also shares code: its networks,
   bipartitions and objective are the same code, reformatted, and its BFGS search is SciPy's
   BFGS with the same gradient tolerance (1e-12) from the same first predictor. Its seed (1811
   against 20261118), its random restarts (12 at standard deviation 0.7 against 6 at 0.5) and
   its iteration cap (50000 against 20000) are its own. Neither cap is reached on the four
   networks: no BFGS run of either script takes more than 21 iterations there. The alternating
   scheme is code of its own. It is a different algorithm, not an independent implementation of
   the whole check, and alone it gives, to seven decimals, the same values as the value kept and
   as BFGS alone. Version 1.1 says this in the caption of Table 6 and archives the
   check as `python/numeric/segundo_optimizador.py` (Section 5 below). The sentence of the AI
   declaration that said the check was not archived is removed, here and in `README.md`.
2. **"Confirms" becomes "illustrates".** The abstract and the introduction of version 1.0 said
   that the four-unit networks *confirm* where the bridges commute and where they break. Computed
   values of J are upper bounds, and the pattern of commutation follows from Lemma 29 (28) and the
   Lean checks, not from them. Version 1.1 says *illustrates*, in the paper and in the archive's
   copies of the abstract and summary (`README.md` and its Spanish summary, `.zenodo.json`,
   `metadata/zenodo_metadata.md`). The exact two-unit results, such as the attainment of the
   min-cut lower bound, are still stated as shown exactly. The title of Act II, "Validation in a
   Gaussian laboratory", is kept.
3. **Rounding of printed values.** Version 1.0 called the values of J "the least value found"
   and "not a certificate", but did not say what follows. Version 1.1 says it in the definition of
   the label [N] (Section 1.2), in Section 5.4 and in the caption of Table 6. Before it is rounded
   for printing, a value of J found by local optimization is the objective at a candidate
   predictor, so it is an upper bound for J, and the value of I_cut = I_pred − J computed from it
   is a lower bound for I_cut. A printed value can fall below J by up to half a unit in its last
   digit. No more than this is claimed. The values of J in Table 4 (3) are marked as numerical
   upper bounds whose signs are given by Lemma 29 (Section 3.5).
4. **Scope of Theorem 51(c) (Theorem 50(c)).** Version 1.0 stated part (c) as: if k = κ(s) and
   k′ = κ(s′) are realized classes and k is not reachable from k′, there is an f, monotone along
   the edges, with f(k) ≠ f(k′), "hence u(s) ≠ u(s′)". The letter f also named the factor of
   u = f∘κ, and the conclusion could be read as a statement about the unity degree u of Q.
   Version 1.1 states the order of the quantifiers: for every class 𝒯, descriptor Φ_Q and map κ,
   and for all realized classes k = κ(s) and k′ = κ(s′) with k not reachable from k′, there is a
   function g on the classes, monotone along the edges, with g(k) ≠ g(k′). The function g depends
   only on the digraph and on k′: it is the indicator of the classes reachable from k′. Then g∘κ
   satisfies IM_𝒯 and takes different values at s and s′. A new paragraph, "Scope of Theorem 51",
   says that g is a mathematical construction and that g∘κ is not identified with u. It also says
   that no part of the theorem or of its Lean checks examines a physically specified class 𝒯 with
   the original descriptor Φ_Q. The theorem now has a paper proof [A], which holds for real values.
   Its labels are also corrected. Version 1.0 said that "all three parts" are compiled in Lean
   [L]. In fact `ViaFutura.lean` compiles part (a) for the intervention digraph and parts (b) and
   (c) only for an abstract digraph, with integer-valued degrees [L]. The three parts in the form
   stated, with real-valued degrees, are [M], in `FrontierReal.lean` (Section 5 below).
5. **Theorem 33 (32), reconstruction.** Version 1.0 said that **Open** can be recovered from its
   projections, up to isomorphism. The Lean criterion `reconstruction_iff_injective` is a statement
   about maps on the set of isomorphism classes. Version 1.1 restricts the theorem accordingly:
   the isomorphism classes of objects of **Open** can be recovered from the joint projection. A
   remark after the theorem says that the criterion recovers objects up to isomorphism, not the
   groupoid or its automorphisms. Table 8 (7) is aligned with this.
6. **Codomains of F_GNWT and F_FEP (Sections 3.2 and 3.5).** Version 1.0 listed the set of hubs
   among the isomorphism-invariant assignments into discrete categories, and drew F_GNWT with
   codomain 𝒫(V). The set of hubs is carried along by isomorphisms, not invariant under them.
   Version 1.1 defines F_GNWT(X) = |Hub(X)| ∈ ℕ, the number of hubs. Hub is a functor into the
   groupoid of finite sets and bijections, and the bridge map is G_GNWT(m) = [m > 0], so that the
   composite is the presence of a hub. The pair (ρ, p_X) of F_FEP is labelled by the units and
   their states, so it is not invariant either. Version 1.1 says that the invariant FEP-type
   assignment is its isomorphism class, with the mutual information, or the mutual information
   alone. The paper also states which of these readings Lean formalizes: the presence of a hub,
   as a Boolean, and its absence. No Lean statement counts hubs.
7. **One comparison ψ against every ψ (remark after Theorem 23, Sections 2.5 and 2.7).** Some
   sentences of version 1.0 could be read as requiring relational sufficiency,
   ker Φ_Q ⊆ ker 𝔘, for a single comparison ψ. For one specified ψ, S_u for u = ψ∘𝔘 is
   ker Φ_Q ⊆ ker(ψ∘𝔘). It can hold, with u not constant, although Φ_Q does not determine 𝔘.
   Relational sufficiency is necessary for S_u with every ψ (Theorem 23), and for S_u with one ψ
   that takes different values on any two distinct structures occurring in one fibre of Φ_Q, such
   as an injective ψ.
8. **Smaller corrections.**
   - Figure 1 moves the premise Rob from the physical results to the psychophysical premises.
   - A14–U is called a stipulation of Q, not "an adopted decision" (Section 2.7).
   - The list of unjustified premises in Section 2.7 now includes Rob, the absence anchor, TL and
     the selection law SEL.
   - The text after Definition 3 (Section 2.1) and the description of Figure 1 (Section 2.3) no
     longer say that the paper does not treat descent at all: they point to the conditional
     criterion of Section 2.8.
   - A cross-reference in Theorem 42 (41)(b) now points to Section 3.2, where the functor Hub is
     defined.
   - The methodological guide (Section 6.4) adds that whether IIT and GNWT themselves disagree on
     the band is an empirical question.
9. **The cohomological paragraph of Section 6.1.** Version 1.0 did not state the base space, the
   coefficients or the scope of the conclusion. Version 1.1 states them:
   - The base is the codomain ℝ of Φ_Q, and the presheaf of local factorizations is a sheaf of
     sets.
   - S_u is a condition on its stalks, not a gluing condition, so there is no class in H¹ to
     detect.
   - A second construction, with coefficients in a group of rescalings of the degree over the
     space of systems of **Open**_G, is kept apart.
   - The vanishing of H¹ is limited to that star-shaped space and to constant coefficients. It
     concerns neither D_0 nor the space of isomorphism classes. A counterexample with coefficients
     that are not locally constant, the extension by zero j_!ℤ, shows why.

## 2. Exposition

- **Q itself (Section 1.1, Limitations).** The list of decisions that the author has not taken
  now includes the grain γ and the form of the comparison relation (a ψ, or a substitute), as
  Section 2 already did; `README.md` is aligned with it.
- **Three things kept apart (Section 1.2).** A conditional result, the justification of its
  premises, and an empirical validation, which would need a measurement channel for u calibrated
  independently of Φ_Q. Definition 5(c) adds that an observable that is a function of Φ_Q cannot
  test S_u.
- **Table 3 (new)** separates the kinds of item on which a derivation of the obligations of Q
  would rest: the author's specification decisions (D_0, γ, Φ_Q, the comparison relation, the
  reading of 𝒞), the stipulations of Q (A9–U, A14–U), the substantive premises examined (none
  adopted or justified), and the results, each conditional on its hypotheses.
- **After Theorem 19, and in Section 2.4.** The entailment criterion is abstract. The open task
  for the original descriptor is to find a relation R whose pairs each have a defense of their
  own and whose generated equivalence contains ker Φ_Q, non-isomorphic realizations included. A
  relation contained in ker Φ_Q that connects each fibre, with fewer pairs, makes the premises
  jointly equivalent to S_u.
- **The order clause does not reach the residual (Section 2.2, after Theorem 15; unnumbered,
  [A]).** Admissibility, the constancy of u on isomorphism classes and the order clause B
  together entail S_u for every compatible degree if and only if every fibre of Φ_Q is a single
  isomorphism class. Two finite countermodels show the scope; they violate S_u, so they are
  neither models of Q nor empirical counterexamples to it.
- **SEG (Section 2.7).** Being equivalent is not being circular: what is missing is a defense of
  SEG, or of non-degenerate S_u, of its own, not another formulation.
- **Proposition 44 (43).** The conclusion concerns the unity component alone; the other
  obligations of Q are untouched.
- **The proxies (abstract, Sections 1.1, 3.2, 5 and Table 5 (4)).** J is not the Φ of IIT 3.0.
  The broadcast hub is a structural stand-in that models neither the ignition of GNWT nor its
  dynamic broadcast. It is read on the undirected graph of the support, which is an adequate
  stand-in for broadcast only on symmetric supports; the statements that depend on this reading,
  such as the emptiness of the band for n ≤ 3, are stated for it.

## 3. Numerical clarifications

- The definition of [N] (Section 1.2), Section 4.1, Section 5.4 and the caption of Table 6 state
  the principle of Section 1.3 above. A numerical check L ≤ J against a proved lower bound L, such
  as the lower side of the min-cut sandwich or the hub bound, cannot fail through optimization
  error and adds no evidence for the theorem, which rests on its proof and its Lean check. The
  upper side of the sandwich holds by construction, because the search starts from the predictor
  of the proof. A computed 0 is exact only on a disconnected support, as for the split network
  and the tensor products (Lemma 29, Proposition 31).
- Section 4: the stationary mutual information of the block-diagonal example is given exactly,
  ½ log(1600/1033) ≈ 0.2188 nats. The values w_min = 0.36 and 0.765 for C_4 hold with its units
  numbered along the cycle. The two values of J there are equal by isomorphism invariance, and
  their numerical value is that of Table 4.
- Remark 53 (52) says which matrix can be indefinite: S = WQAᵀ + AQWᵀ + 2cE of the proof of
  Proposition 52(b), with Q = c²P(c). Its eigenvalues are about −0.0281 and 4.1568 at c = 0.33,
  and −0.0098 and 4.8336 at c = 0.38. `contraejemplo_diagonal_fija.py` now computes S exactly,
  prints its eigenvalues and checks, exactly, that det S < 0 at both values [S]. The remark also
  says how the minimum is found and what is not certified:
  - the coercive polynomial is the residual determinant det(E + (A − B)P(A − B)ᵀ), of which the
    objective is an increasing function, and the minimum is taken over its real critical points,
    not by a local optimizer;
  - what is not certified is that the root finding, with its residual filter, finds all of them;
  - unlike the other conclusions drawn from computed values of J, the decrease is not implied by
    any proof in the paper.
- Section 6.3: the grids in c and t illustrate Proposition 52 and do not check it, since each
  computed value is only an upper bound.

## 4. Verification of inherited results

In preparing version 1.1, the checks of version 1.0 were rerun on copies of its archive, which
verified against its `SHA256SUMS` (83 of 83 files).

- The six Lean files without Mathlib compile with Lean 4.24.0, with exit code 0 and with outputs
  identical to `lean/expected/`: 57 reports. The five auxiliary lemmas cited without a printed
  report (`cm1_OI`, `cm1_Adm`, `cm2_factor`, `zmul_unit_left`, `zmul_unit_right`) depend on no
  axioms.
- The seven modules of the Lean project with Mathlib compile against Mathlib v4.24.0 (commit
  `f897ebcf`), with outputs identical to `lean-mathlib/expected/`: 73 reports, all
  `[propext, Classical.choice, Quot.sound]`.
- The eleven Python scripts pass `python/verify_python.sh`, with the 156 exact checks and the
  band counts 0, 0, 15 and 472.
- `make pdf` on the version 1.0 archive rebuilds a PDF whose text is identical to that of the
  archived PDF.

These reruns were done by agents of the same assistant; they are not an independent validation.

## 5. New results and new files

- **Theorem 26 (Section 2.8, new): conditional discharge of the sufficiency, order and descent
  obligations** [A] [L]. It states which premises would entail each sufficiency obligation S_x
  (x ∈ {c, q, u, τ, σ}), the order clause B and the descent condition O, without changing the
  domain, the descriptor, the components or the obligations of Q, and it establishes none of
  these premises. Its five parts are:
  - (i) bridge premises with coverage, ker d_x ⊆ ⟨R_x⟩, for each component, with the converse;
  - (ii) unity through the coexperience structure: relational sufficiency gives S_u for every ψ;
    it is necessary for S_u with every ψ, and for S_u with one ψ that takes different values on
    any two distinct structures sharing a fibre of Φ_Q (for instance an injective ψ), but not in
    general for one given ψ, even with u not constant;
  - (iii) premises of order type, with exact criteria for S_u, B and S_u ∧ B;
  - (iv) intervention monotonicity as a premise: it entails S_u for every compatible degree only
    when Φ_Q is injective on D_0;
  - (v) descent along a relation ∼, and its exactness.

  A paragraph after the theorem treats the quality component under the pointed reading of 𝒞 [A]
  [L]. The abstract form is checked in the new file `lean/CondicionalQ.lean` (Lean 4 core, no
  Mathlib; namespace `CondicionalQ`), whose 28 printed theorems are listed in Table 7 and
  Appendix B. Its values lie in arbitrary types and, in parts (iii) and (iv), its degrees take
  values in a scale, a partial order with two values lo < hi; the integers are an instance
  (`intScale`), and the real numbers are an instance that is not compiled, since Lean without
  Mathlib has no real numbers. `conditional_discharge` combines parts (i), (iii)(b) and (v), and
  `conditional_discharge_nonvacuous` gives a model on three realizations in which its bridge,
  coverage and order premises hold with u not constant.

  Theorem 26 is also summarized in the abstract, in item (R1) of Section 1.1 and in a new (R1)
  row of Table 1 ([A], [L]; `conditional_discharge`, `conditional_discharge_nonvacuous`). Each
  says which premises would discharge the sufficiency obligations, the order clause B and the
  descent condition O, and that no premise is justified.
- **Theorem 51 (50) with real-valued degrees** [M]. The new module
  `lean-mathlib/QAuditAnalytic/FrontierReal.lean` (namespace `QAuditFrontier`) proves the three
  parts as instances of statements for degrees in an arbitrary order. The order hypotheses are
  stated as sufficient conditions:
  - (a) holds for any relation ≤ (`im_iff_edges`);
  - (b) is proved for partial orders (`constant_on_scc`); a separate proof uses only transitivity and
    antisymmetry (`b_transitive_antisymmetric`), and neither can be dropped: `b_needs_antisymmetry`
    and `b_needs_transitivity` are counterexamples;
  - (c) is proved for preorders with two values w₀ < w₁ (`nonconstant_if_not_scc`). Its ≠ form
    needs only two distinct values w₀ ≠ w₁ with w₀ ≤ w₁ and reflexivity at them
    (`c_ne_of_two_values`; `c_ne_without_strict_pair`), and it fails in the discrete order on two
    values, where no two distinct values are comparable (`c_fails_discrete_order`); the general
    case is the same one-line argument and is not compiled.

  No minimality is claimed beyond these counterexamples. The module also contains:
  - `frontier_real`, the three parts with real-valued degrees and the quantifiers in the order of
    the theorem;
  - `frontier_c_uniform_real` and `nonconstant_uniform`, which show that one function g, chosen
    from the digraph and k′, serves for every class not reachable from k′;
  - `frontier_paper_form` and `escape_paper_form`, with the digraph on the realized classes im κ,
    as in the paper. Lean's digraph has every class as a vertex, and the difference is harmless;
  - `escape_iff_real`, the sentence after the theorem;
  - `empty_domain_convention`: with no realizations the empty digraph counts as strongly
    connected;
  - `Example.nonvacuous` and `Example.pi_degree`, the non-vacuity checks;
  - the definitions of reachability and of the intervention digraph, copied verbatim from
    `ViaFutura.lean`, with a proof that this reachability is Mathlib's `Relation.ReflTransGen`.

  Two lemmas of the review files are renamed so that their names do not suggest minimality:
  `c_minimal` becomes `c_ne_of_two_values`, and `c_needs_strict_pair` becomes
  `c_fails_discrete_order`.
- **The second check of Table 6, archived.** `python/numeric/segundo_optimizador.py` repeats
  section (1) of `verif_gauss.py` exactly, with the same seed, the same random restarts in the
  same order, the same BFGS options and the same alternating scheme. Its kept values are
  identical, bit for bit, to those of the original check, and the lines that the original check
  printed are reproduced character for character. For each network it prints, to seven decimals,
  the value kept, and separately the value of the alternating scheme alone and the value of BFGS
  alone. It checks internally that each agrees to seven decimals with the values that the
  original check printed, 0.2212930, 0.1134987, 0.1058709 and 0.0000000 (version 1.0 cited only
  their agreement to seven digits, not the values). It also
  checks, with a relative tolerance of 1e-12 (absolute 1e-15 near 0), that the alternating
  scheme never increases the objective. Its output is identical across runs and thread settings.
  It is a numerical illustration [N], not a certificate.

### Files of the archive

- Added:
  - `CHANGES.md`;
  - `lean/CondicionalQ.lean` and `lean/expected/salida_CondicionalQ.txt`;
  - `lean-mathlib/QAuditAnalytic/FrontierReal.lean` and
    `lean-mathlib/expected/salida_FrontierReal.txt`;
  - `python/numeric/segundo_optimizador.py` and
    `python/expected/salida_segundo_optimizador.txt`.
- Changed:
  - `paper/` (the LaTeX sources and a PDF built from them);
  - `lean/verify_lean.sh` (seven files);
  - `lean-mathlib/QAuditAnalytic.lean` (imports `FrontierReal`);
  - `lean-mathlib/verify_mathlib.sh` (eight modules in both loops);
  - `python/verify_python.sh` (twelve scripts);
  - `python/high_precision/contraejemplo_diagonal_fija.py` and its expected output (the
    eigenvalues of S and the sign of det S, and a final verdict line);
  - `README.md`, `CITATION.cff`, `.zenodo.json`, `metadata/zenodo_metadata.md`, `Makefile`,
    `verify_all.sh`, `LICENSE` (version line) and `SHA256SUMS`.
- Unchanged:
  - the six Lean files of version 1.0 and their expected outputs;
  - the seven Mathlib modules of version 1.0 and their expected outputs;
  - `lakefile.toml`, both `lean-toolchain` files and `lake-manifest.json`, which pins Mathlib
    v4.24.0;
  - ten of the eleven scripts of version 1.0, with their expected outputs;
  - `python/compare_outputs.py`, `python/requirements.txt`, `.gitignore` and `.gitattributes`.

Counts, computed from the compiled outputs and the files:

| | Version 1.0 | Version 1.1 |
|---|---|---|
| Lean files without Mathlib | 6 | 7 |
| … their printed theorems (`#print axioms`) | 57 | 85 (57 + 28 in `CondicionalQ.lean`) |
| Modules of the Lean project with Mathlib | 7 | 8 |
| … their `#print axioms` reports | 73 | 104 (73 + 31 in `FrontierReal.lean`) |
| Mathlib reports with `[propext, Classical.choice, Quot.sound]` | 73 | 92 |
| Mathlib reports with no axioms / with `propext` alone | 0 / 0 | 11 / 1, all in `FrontierReal.lean` |
| Python scripts | 11 | 12 |

The axioms of the 85 theorems are, by pattern:

| Theorems | No axioms | `propext` | `Quot.sound` | `propext`, `Quot.sound` | all three |
|---|---|---|---|---|---|
| First six files (57) | 33 | 13 | 0 | 3 | 8 |
| `CondicionalQ.lean` (28) | 12 | 2 | 2 | 0 | 12 |

Every Lean file and module uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`, compiles with exit code 0 and contains no `sorry`, `admit`, `native_decide`,
`axiom` or `opaque` declarations.

## 6. What did not change

- The domain D_0, the descriptor Φ_Q, the components of Q, the meaning of the unity degree u and
  the obligations of Q.
- The scope: Q is neither demonstrated nor refuted, and the audit concerns explicit structural
  proxies of the theories, not the theories themselves.
- The three acts and their titles, and the main results of version 1.0 with their status
  labels, apart from the statements corrected or narrowed in Section 1.
- No check of version 1.0 changed its outcome. No archived Lean statement of version 1.0 was
  modified, and the printed values of Table 6 (Table 5 in version 1.0) are unchanged.

## 7. What remains open

- Every obligation of Q:
  - the five sufficiency obligations S_u, S_c, S_q, S_τ and S_σ;
  - the order clause B;
  - the descent condition O along a physical equivalence constructed independently of Q;
  - joint admissibility;
  - the obligations on processes, among them P_branch and P_arr.
- The specification decisions, which only the author can take: D_0, the grain γ, Φ_Q, the
  comparison relation for the degree (a ψ, or a substitute) and the reading of 𝒞.
- The premises of Theorem 26 are psychophysical hypotheses or physical tasks that the paper does
  not justify. In particular, a relation that covers the fibres of Φ_Q and whose pairs each have
  a defense of their own has not been found. Theorem 26 shows what would suffice, not that it is
  available.
- Theorem 51 concerns mathematical degrees. That the original degree is of the form f∘κ and
  satisfies IM_𝒯, a comparison relation for the degree, a measurement of u along the
  interventions, and a physically specified class of interventions for the original Φ_Q are all
  unavailable.
- The numerical values of J are upper bounds, not certified minima.
- The Lean statements on exact covariance and on the order clause in `ViaFutura.lean` take
  integer values, and their transcription to real values is not formalized. The statements that
  Section 6.5 lists for formalization remain to be formalized.
- There has been no independent human review of version 1.0 or of version 1.1.
