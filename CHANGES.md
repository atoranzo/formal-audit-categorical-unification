# Changes from version 1.0 to version 1.1

*A Formal Audit of a Categorical Unification of Consciousness Theories: Structural Proxies,
Formal Obstructions and a Positive Route*, preprint and verification archive, version 1.1,
19 November 2026. Not peer reviewed.

Version 1.0 is deposited on Zenodo with the DOI
[10.5281/zenodo.24349944](https://doi.org/10.5281/zenodo.24349944) (GitHub tag `v1.0`) and is
not modified. Version 1.1 receives its own DOI when it is released; until then the concept DOI
[10.5281/zenodo.24349943](https://doi.org/10.5281/zenodo.24349943), which resolves to the latest
version, is used wherever a DOI for the current version is needed.

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
  - (b) is proved for partial orders (`constant_on_scc`); its proof uses only transitivity and
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
- The numerical values of J are upper bounds, not certified minima. The decrease of Remark 53
  rests on a root finding whose completeness is not certified.
- The Lean statements on exact covariance and on the order clause in `ViaFutura.lean` take
  integer values, and their transcription to real values is not formalized. The statements that
  Section 6.5 lists for formalization remain to be formalized.
- There has been no independent human review of version 1.0 or of version 1.1.
- The DOI of version 1.1 is assigned when it is released.
