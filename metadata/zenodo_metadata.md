# Zenodo deposit: metadata

Fields for the Zenodo upload form. They are also in machine-readable form in `../.zenodo.json`
and `../CITATION.cff`. If the record is created from GitHub through the Zenodo integration, Zenodo reads `.zenodo.json`.

## Basic information

| Field | Value |
|---|---|
| Resource type | Publication → Preprint |
| Title | A Formal Audit of a Categorical Unification of Consciousness Theories: Structural Proxies, Formal Obstructions and a Positive Route |
| Publication date | 2026-11-18 |
| Version | 1.0 |
| Language | English |
| Creators | Toranzo Portela, Ángel José; affiliation: Independent Researcher in Theoretical Physics and Cognitive Science |
| License | Creative Commons Attribution 4.0 International (CC BY 4.0), chosen by the author. The class file `compositionalityarticle.cls` keeps its own license, LPPL 1.3c. |
| Access | Open |
| Files | Either create the record from the GitHub release (Zenodo archives the repository as one zip), or upload `formal-audit-categorical-unification-v1.0.zip` by hand. Do not upload the files one by one: Zenodo keeps a flat list of files, and the README, the verification scripts and `SHA256SUMS` rely on the folder structure. Optionally, also upload the PDF on its own so that Zenodo shows a preview. |

## Description (abstract)

Several theories of consciousness, among them integrated information theory (IIT), global neuronal workspace theory (GNWT) and attention schema theory, together with general frameworks that have been brought to bear on consciousness, such as the free-energy principle (FEP) and quantum Darwinism, describe the same open physical systems through different invariants. A candidate theory, Q, formulated by the author and defined in this paper, proposes to unify them categorically. We audit this unification formally and structurally, to delimit with mathematical precision which parts of it can be established and which promises of unification fail, for explicit structural proxies of the theories, not for the theories themselves. The test case is the unity-sufficiency obligation S_u of Q; the audit does not change the descriptor, the domain or the meaning of Q. Results are labelled by their evidence: proofs checked by the Lean 4 kernel, paper proofs, exact computation, or numerics.

(I) Negative delimitation. The weak categorical thesis holds, but cheaply: every isomorphism-invariant assignment is a functor out of a symmetric monoidal groupoid of open systems. For the presence proxies of IIT type (a Gaussian integration functional J > 0) and GNWT type (a broadcast hub) there is no translation between the projections, their bridge square does not commute, and neither is monoidal into the additive reals: both vanish on systems with disconnected support, in particular on tensor products of nonempty systems, and with the empty system sent to an adjoined unit they are strong monoidal into a zero-product monoid, whereas predictive information is additive. The two proxies disagree exactly on a band of connected systems without a hub, empty for n ≤ 3 units and containing the path P_n and the cycle C_n for every n ≥ 4. A premise “the degree depends only on κ” implies S_u exactly when the kernel of the descriptor lies in the equivalence it generates, and none of the principles examined closes S_u without presupposing it, equating only isomorphic realizations, forcing a constant degree, changing the meaning of the degree, or changing the domain.

(II) A Gaussian laboratory, exact in a two-unit family and numerical in four-unit networks, confirms where the bridges commute and where they break, and shows exactly that the min-cut lower bound on J is attained.

(III) Of the reformulations examined, only intervention monotonicity escapes the collapse; it is a declared weakening of the order clause of Q, not S_u, and we have not shown that it is the only one. Degrees are forced to be constant exactly on the strongly connected components of an intervention digraph. With J as a stand-in for the descriptor of Q, on systems with at least two units J increases strictly under uniform scaling of any connected dynamics, or with a fixed scalar self-coupling (checked in Lean with Mathlib, as are the equivalence of J > 0 with connected support and the min-cut bounds on J), but numerically it can decrease against a fixed non-scalar self-coupling.

Q is neither demonstrated nor refuted. Six Lean files without Mathlib and a Lean project with Mathlib of seven modules, all without sorry, and eleven scripts archived with the paper reproduce every result labelled as checked by Lean, by exact computation or numerically.

This record contains:
- the paper, as a PDF and as LaTeX source in the Compositionality template, with the `unpublished` option;
- six Lean 4 files, checked with Lean 4.24.0 without Mathlib: exit code 0, no `sorry`, and only the standard axioms;
- a Lean 4 project with Mathlib v4.24.0 (seven modules) that checks three analytic results on J: the connectivity lemma, the min-cut sandwich and the scaling proposition, with only the standard axioms;
- eleven Python scripts (exact SymPy computations, numerical illustrations and exact counts) with their expected outputs;
- three scripts that rerun everything and compare the results, and a master script, verify_all.sh (or make verify), that first checks the SHA-256 sums of all files and then runs them in turn (see README.md).

Use of generative AI: the paper was drafted, and its Lean files and scripts were written and run, by an AI assistant (Claude Code, by Anthropic, with Anthropic's Claude models), at the request and under the direction of the author, who is responsible for the content. Agents of the same assistant read primary sources, verified the Gaussian family, translated the paper from its Spanish master version, formalized the analytic results in Lean with Mathlib and reviewed the work adversarially; their agreement is not an independent validation, and there has been no independent human review. During the research the author also used another AI system in exploratory conversations; that material was treated as unverified input, and no result of the paper depends on it. Only the statements labelled [L] or [M] are checked by the Lean kernel, in their logical form, and only those labelled [S] by exact computation.

## Short abstract (arXiv form, at most 1920 characters; this one has 1907)

Several theories of consciousness (IIT, GNWT, attention schema theory) and frameworks brought to bear on it (the free-energy principle, quantum Darwinism) describe the same open physical systems through different invariants. A candidate theory Q, formulated by the author, proposes to unify them categorically. We audit this unification for explicit structural proxies of the theories, not for the theories themselves, with the unity-sufficiency obligation S_u of Q as test case, and we keep Lean-checked statements, paper proofs, exact computations and numerics apart. (I) The weak categorical thesis holds but is cheap. For the presence proxies of IIT type (a Gaussian integration functional J > 0) and GNWT type (a broadcast hub) there is no translation, the bridge square does not commute, and neither is monoidal into the additive reals; they disagree exactly on connected systems without a hub, a band empty for n ≤ 3 that contains P_n and C_n for n ≥ 4. Premises “the degree depends only on κ” imply S_u exactly when the kernel of the descriptor lies in the equivalence they generate, and none of the principles examined closes S_u without circularity, collapse, or a change of meaning or domain. (II) A Gaussian laboratory, exact in two units and numerical in four, confirms where the bridges commute and break and that the min-cut lower bound on J is attained. (III) Of the reformulations examined, only intervention monotonicity, a declared weakening of the order clause of Q, escapes the collapse: degrees are forced to be constant exactly on the strongly connected components of an intervention digraph, and J, taken as a stand-in that is not the descriptor of Q, increases strictly, for at least two units, under uniform scaling of any connected dynamics (checked in Lean with Mathlib). Q is neither demonstrated nor refuted. Lean files with and without Mathlib and eleven scripts are archived.

## Keywords

category theory; applied category theory; consciousness; unity of consciousness; integrated information theory; global neuronal workspace theory; free-energy principle; bridge laws; formal verification; Lean 4; Mathlib; SymPy; linear-Gaussian systems; Markov categories

## Additional fields

| Field | Value |
|---|---|
| Notes | Preprint, not peer reviewed. Intended for submission to Compositionality. Not accepted there, so the journal masthead and the class's acceptance mode are switched off. |
| Software | Lean 4.24.0; Mathlib v4.24.0; Python 3.13; NumPy 2.5; SciPy 1.18; SymPy 1.14; mpmath 1.3 |
