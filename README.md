# A Formal Audit of a Categorical Unification of Consciousness Theories: Structural Proxies, Formal Obstructions and a Positive Route

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24349943.svg)](https://doi.org/10.5281/zenodo.24349943)

**Ángel José Toranzo Portela** · Independent Researcher in Theoretical Physics and Cognitive Science\
Preprint and verification archive · version 1.1 · 19 November 2026 · not peer reviewed\
Repository: <https://github.com/atoranzo/formal-audit-categorical-unification>\
Zenodo: all versions (concept DOI, which resolves to the latest version), DOI [10.5281/zenodo.24349943](https://doi.org/10.5281/zenodo.24349943); version 1.0, DOI [10.5281/zenodo.24349944](https://doi.org/10.5281/zenodo.24349944); the DOI of version 1.1 is assigned when it is released\
Changes from version 1.0: [`CHANGES.md`](CHANGES.md)

This archive contains the paper and everything needed to check its machine-verified
claims:
- seven Lean 4 files checked without Mathlib (logic and finite combinatorics), among them
  `CondicionalQ.lean`, new in version 1.1, for the conditional theorem of Section 2.8
  (Theorem 26);
- a Lean 4 project with Mathlib, of eight modules: three analytic results on the Gaussian
  integration functional J (the connectivity lemma, the min-cut sandwich and the scaling
  proposition) and, new in version 1.1, the exact frontier of intervention monotonicity
  (Theorem 51) with real-valued degrees, in `FrontierReal.lean`;
- twelve Python scripts (exact SymPy computations, exact enumerations and numerical
  illustrations) with their expected outputs, among them `segundo_optimizador.py`, new in
  version 1.1: the second check of the four-unit networks that version 1.0 cited without
  archiving it;
- three scripts that rerun everything and compare the results, and a master script,
  `verify_all.sh` (or `make verify`), that first checks the SHA-256 sums of all files and
  then runs the three.

The paper is self-contained: every definition, hypothesis and result it uses is stated in
it.

## What the paper does

Several theories of consciousness, among them integrated information theory (IIT), global
neuronal workspace theory (GNWT) and attention schema theory, together with general
frameworks brought to bear on consciousness, such as the free-energy principle (FEP) and
quantum Darwinism, describe the same open physical systems through different invariants.
A candidate theory, Q, formulated by the author and defined in Section 2 of the paper,
proposes to unify them categorically: each theory as a functor out of a common category of
open systems, connected by natural transformations, limits or bridge laws. The paper audits
that proposal (a self-audit) for explicit structural proxies of the theories, not for the
theories themselves. Its test case is the unity-sufficiency obligation S_u of Q,
Φ_Q(s) = Φ_Q(t) ⇒ u(s) = u(t), and the audit changes neither the descriptor, nor the domain,
nor the meaning of Q.

The argument has three acts.

1. **Negative delimitation.**
   - The weak categorical thesis (every isomorphism-invariant assignment is a functor out of
     one symmetric monoidal groupoid of open systems) holds, but cheaply: it holds for any
     family of invariants and decides no dispute between the theories.
   - The strong thesis fails for the structural presence proxies of IIT type (a Gaussian
     integration functional J > 0, not the Φ of IIT 3.0) and GNWT type (a broadcast hub of the
     undirected coupling graph, a structural stand-in that models neither ignition nor dynamic
     broadcast). There is no translation between them, their bridge square does not commute,
     and neither is monoidal into the additive monoid of [0, +∞]. They disagree exactly on a
     band of connected systems without a hub, which is empty for n ≤ 3 units and contains the
     path P_n and the cycle C_n for every n ≥ 4.
   - Premises of the form "the degree depends only on κ" imply S_u exactly when ker Φ_Q is
     contained in the equivalence they generate. The criterion says which relations would
     suffice, not that one is available.
   - None of the candidate principles examined closes S_u without one of five moves:
     presupposing it, equating only isomorphic realizations, collapsing the degree to a
     constant, changing the meaning of the degree, or changing the domain. With the degree a
     function of the coexperience structure, the banded segregation SEG is non-degenerate
     S_u itself, rewritten in testable form.
   - A conditional theorem (Theorem 26, Section 2.8, new in version 1.1) states which premises
     would discharge the five sufficiency obligations, the order clause B and the descent
     condition O of Q. It establishes none of them, and it changes neither the domain, nor the
     descriptor, nor the components, nor the obligations of Q.
2. **Validation in a Gaussian laboratory.** In two-unit linear-Gaussian families (exactly,
   with SymPy) and in four-unit networks (numerically), the paper examines four things:
   - where the bridges commute and where they break, for the undirected reading of the hub
     (the band needs four units, so the breaking is illustrated on the four-unit networks,
     whose computed values of J are upper bounds; the pattern itself follows from the
     connectivity lemma and the Lean checks);
   - that the min-cut lower bound on J is attained (exactly);
   - that predictive information is additive while J vanishes on tensor products of
     nonempty systems, so that J is not monoidal into the additive monoid and, with the
     empty system sent to an adjoined unit, is strong monoidal into a zero-product monoid;
   - that selecting the state of minimal surprisal (a free-energy-type selection) is
     trivial on laws and, on states, discards almost every realization: it selects the
     mode, which has probability zero.
3. **A positive route.**
   - Of the reformulations of S_u examined, only intervention monotonicity escapes the
     collapse. It is not S_u, nor an obligation of Q, but a declared weakening of Q's order
     clause to a class of interventions on one system, and it has not been shown to be the
     only reformulation that escapes.
   - Its exact frontier (Theorem 51): degrees are forced to be constant exactly on the
     strongly connected components of an intervention digraph on the realized classes. This
     is a statement about mathematical degrees; the function that separates two components is
     a mathematical construction, not identified with the unity degree u of Q.
   - In the band it can be instantiated with J in place of the descriptor Φ_Q, which is not
     justified: for at least two units, J increases strictly under uniform scaling of a
     connected dynamics, and
     under scaling of the couplings with a fixed scalar self-coupling (checked in Lean with
     Mathlib). Numerically, J can decrease if the fixed self-coupling is not scalar.

Q is neither demonstrated nor refuted.

## Status labels

| Label | Meaning |
|---|---|
| **[L]** | checked by the Lean 4 kernel (Lean 4.24.0, no Mathlib): logic and finite combinatorics |
| **[M]** | checked by the Lean 4 kernel with Mathlib (v4.24.0): over real matrices and, for Theorem 51, with real-valued degrees |
| **[A]** | proved on paper in the paper; alone, not formalized (**[A] [M]**: a paper proof whose statement is also checked with Mathlib) |
| **[S]** | verified exactly by computer (SymPy 1.14, or exact integer enumeration) |
| **[N]** | numerical illustration, not a certificate: a computed value of J is, before rounding, an upper bound for J, and a printed value can fall below J by up to half a unit in its last digit |

For [L] and [M]: exit code 0, no `sorry`, `admit`, `native_decide`, `axiom` or `opaque`
declarations, no kernel-bypassing options, and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. Where a result in Sections 2–4 of the paper carries no
explicit label, the name of a Lean theorem marks a statement checked in the abstract form
stated next to it: names in a namespace that begins with `QAudit` are [M], the others [L].
Table 1 of the paper gives the label of each main result and the Lean theorem or script
that checks it; Appendix A gives the complete correspondence between results, Lean
theorems and scripts.

What is checked with Mathlib: the connectivity lemma (J > 0 if and only if the support is
connected, for at least two units), the min-cut sandwich exactly as stated, with extreme
eigenvalues, both parts of the scaling proposition, and the three parts of the exact frontier
of intervention monotonicity (Theorem 51) with real-valued degrees, as instances of statements
for degrees in an arbitrary order whose hypotheses are sufficient conditions on that order.
What remains a paper proof includes the hub bound, the additivity of predictive information
and the categorical scheme of Section 3. The conditional theorem of Section 2.8 is a paper
proof whose abstract form is checked in Lean without Mathlib, with values in arbitrary types
and, in its order parts (iii) and (iv), degrees in a scale (the integers are an instance; the
real numbers are an instance that is not compiled).

## Contents

```
README.md                 this file
CHANGES.md                changes from version 1.0
LICENSE                   license of the archive (CC BY 4.0)
SHA256SUMS                checksums of every other file
verify_all.sh             runs every check below, in order, and prints a summary
Makefile                  make verify, make checksums, make verify-lean, make verify-python,
                          make verify-mathlib, make pdf (make help lists them)
CITATION.cff              citation metadata
.zenodo.json              Zenodo metadata (used by the GitHub-Zenodo integration)
.gitignore                files kept out of the repository
.gitattributes            keeps every file byte for byte in git, so that SHA256SUMS verifies
metadata/
  zenodo_metadata.md      fields for the Zenodo upload form, and a short abstract
paper/
  formal_audit_categorical_unification.pdf
  source/                 LaTeX source (main.tex, preamble_en.tex, en/*.tex) and the
                          unmodified Compositionality class compositionalityarticle.cls
lean/                     seven Lean 4 files checked without Mathlib
  lean-toolchain          leanprover/lean4:v4.24.0
  IntentoSu.lean  UnificacionCat.lean  PistasUnificacion.lean
  FiltracionCociente.lean  ViaFutura.lean  GaussConexion.lean  CondicionalQ.lean
  expected/               expected compiler output (#print axioms) for each file
  verify_lean.sh
lean-mathlib/             Lean 4 project with Mathlib v4.24.0
  lakefile.toml  lean-toolchain  lake-manifest.json  QAuditAnalytic.lean
  QAuditAnalytic/         Core, LemmaJ, Scaling, Bridge, Interval, ExamplesLemmaJ,
                          ExamplesScaling, FrontierReal (.lean)
  expected/               expected output (#print axioms) for each module
  verify_mathlib.sh
python/
  requirements.txt
  exact/                  SymPy scripts: Gaussian families and their connections [S]; the
                          identity of the scaling proposition [S], with grids in c [N]
  high_precision/         the fixed-diagonal counterexample (50-digit roots) [N] and the
                          matrix S of Remark 53, exactly, with det S < 0 [S]
  numeric/                four-unit networks and their second check, exact band counts for
                          n = 2..5 [S], and monotonicity grids [N]
  expected/               expected output of each script
  compare_outputs.py      comparison used by verify_python.sh
  verify_python.sh
```

File and script names are those of the original working files, partly in Spanish. So are
some comments and printed messages: "comprobaciones superadas" means "checks passed",
"TODAS LAS COMPROBACIONES: sí" means "ALL CHECKS: yes", and "FALLO" means "FAIL"; the other
printed labels of `segundo_optimizador.py` and `contraejemplo_diagonal_fija.py` are explained
in their headers. Comments point to the items of the paper they check, such as (G1)–(G7) of
Section 5. In
`python/exact/v5_rkp_cadenas.py`, `a` is the paper's a_22 (the driver) and `alpha` the
paper's a (the receiver); the script's header says so. Likewise, in item (C3) of
`python/exact/gauss_conexiones.py`, `a` is the driver's memory, the paper's a_22. Comments
in the Lean files with Mathlib cite the paper by the labels of its LaTeX source, which can be
found in `paper/source/en/`: `lem:J` is Lemma 29 of the PDF (Gaussian integration and
connectivity, which these comments call Lemma J), `thm:cheeger` is Theorem 36 (the min-cut
sandwich), `prop:scaling` is Proposition 52 (monotonicity under scaling), and `thm:frontier`
is Theorem 51 (the exact frontier of intervention monotonicity), in Section 6.2 (`sec:im`),
whose display (13) is `eq:im`. The comments of `lean/CondicionalQ.lean` cite Theorems 15, 19
and 23 and Definitions 3 and 5 by their printed numbers, which are those of version 1.1 and of
version 1.0 alike. Every result numbered 26 or more in version 1.0 has a number one higher in
version 1.1, and every table numbered 3 or more as well (`CHANGES.md` lists them).

## How to verify

All commands in this section are run from the root of the archive, the directory that
contains this README.

### Everything at once

```bash
bash verify_all.sh
```

or `make verify`. The script first checks the SHA-256 sums of all files
against `SHA256SUMS` and stops if a file differs or is missing: the archive is then not the
one that was published. It then runs the three checks described below (Lean without
Mathlib, Python, Lean with Mathlib) and prints a summary; its last line must be
`ALL CHECKS PASSED`. On its first run the Lean project with Mathlib clones Mathlib and its
dependencies and downloads their prebuilt cache (about 1 GB in all), and it needs about
7 GB of free disk; to skip it, run `SKIP_MATHLIB=1 bash verify_all.sh` (or
`make verify SKIP_MATHLIB=1`): the summary then says that the [M] statements were not
checked, and the last line is `ALL CHECKS THAT RAN PASSED (skipped: Lean-with-Mathlib)`.
The exit code of `bash verify_all.sh` is 0 if every check that ran passed, 1 if one failed,
and 2 if one could not run because a tool is missing; `make verify` exits with 0 when the
script does and with make's own error code otherwise. `make help` lists the other targets.

### One check at a time

The same checks can be run one by one. First check the files:

```bash
sha256sum -c SHA256SUMS
```

Every line must end in `OK` (on macOS: `shasum -a 256 -c SHA256SUMS`). The three
verification scripts write their outputs to a temporary directory, never into the archive;
only `lake` creates its build directory, `lean-mathlib/.lake/`, with the Mathlib checkout,
which is not listed in `SHA256SUMS` and is ignored by git.

### Lean without Mathlib (about a minute)

Install Lean with [elan](https://github.com/leanprover/elan). The file `lean/lean-toolchain`
selects Lean 4.24.0 automatically. Then run:

```bash
bash lean/verify_lean.sh
```

If `lean` is not on the `PATH`, give its location with `LEAN=/path/to/lean bash lean/verify_lean.sh`.
For each of the seven files the script refuses forbidden constructs, compiles the file,
requires exit code 0 and compares the printed axioms with `lean/expected/`. The last line must
be `ALL LEAN CHECKS PASSED`.

### Lean with Mathlib (a few minutes, after a download of about 1 GB; about 7 GB of disk)

```bash
bash lean-mathlib/verify_mathlib.sh
```

It needs `lake` (installed with elan), `git`, `curl` and network access to GitHub and to the Mathlib
cache. The first run clones Mathlib and its dependencies into `lean-mathlib/.lake/` and
downloads the prebuilt Mathlib cache with `lake exe cache get` (about 1 GB in all; with the
build, about 7 GB of disk, of which about 0.3 GB in Mathlib's cache directory,
`~/.cache/mathlib` by default); `lake-manifest.json` pins Mathlib to v4.24.0 (commit
`f897ebcf`). The script refuses forbidden constructs, builds the project, recompiles each of
the eight modules and compares the printed axioms with `lean-mathlib/expected/`. The last
line must be `ALL MATHLIB CHECKS PASSED`. The eight modules print 104 `#print axioms`
reports: 92 list `propext`, `Classical.choice` and `Quot.sound`, and the other twelve, all in
`FrontierReal.lean`, list no axioms (eleven) or `propext` alone (one).

### Python (several minutes)

```bash
python3 -m venv .venv && . .venv/bin/activate
pip install -r python/requirements.txt
bash python/verify_python.sh
```

The expected outputs were produced with Python 3.13.17, NumPy 2.5.3, SciPy 1.18.1, SymPy
1.14.0 and mpmath 1.3.0. Every script runs in isolated mode (`python3 -I`) and ends with a
verdict line. `verify_python.sh` passes a script when its exit code is 0, its last line
equals the expected verdict, no line reports a failure, and, for the numerical scripts,
every printed decimal number agrees with the expected output within a relative tolerance of
1e-3 (an absolute one of 1e-6 for numbers below 1e-3 in absolute value), and the output has
the same number of lines and of decimal numbers on each line (integers are not compared
numerically; a wrong count makes the script's own verdict fail). The last line must be `ALL PYTHON CHECKS PASSED`.

`python/numeric/segundo_optimizador.py` repeats the second check of the four-unit networks
(Table 6 of the paper) exactly as it was run for version 1.0, with the same seed. It prints, to
seven decimals, the value of J that the check kept and, separately, the values of its two
methods alone (an alternating weighted least-squares scheme and BFGS), and it checks that each
agrees to seven decimals with the values that the original check printed (version 1.0 cited only
that this check reproduced J to seven digits, not the values).
This check is not independent of `pistas_numerico.py`: it shares the objective, the system
data, the starting predictor and code with it (see the caption of Table 6 and `CHANGES.md`).

### Rebuilding the PDF

```bash
make pdf
```

This runs `pdflatex` three times on `paper/source/main.tex` and writes the result to
`build/paper/main.pdf`, leaving the archived PDF and the sources untouched.

This requires a TeX Live installation with the Latin Modern fonts (`lmodern`), `babel` with
English, `amsmath`, `amssymb`, `amsthm`, `amscd`, `array`, `booktabs`, `graphicx`, `hyperref`,
`caption`, `fancyhdr`, `geometry`, `xcolor`, `xkeyval` and `etoolbox`. The journal class is
included.
This is a preprint, not a paper accepted by Compositionality: the class option `unpublished`
is used, and the preamble switches off the journal masthead and the class's acceptance mode,
so the journal logo is neither needed nor included.

## Scope and limitations

- **Proxies.** J is the Gaussian functional of geometric integrated information, not the Φ
  of IIT 3.0. The broadcast hub is a structural stand-in for global availability, a property
  of the coupling graph that models neither the ignition of GNWT nor its dynamic broadcast; it
  is read on the undirected graph of the support, which makes it an adequate stand-in for
  broadcast only on symmetric supports. The disagreement on the band is a disagreement between
  these proxies, not between the theories as such.
- **Numerics.** The values of J on the four-unit networks come from local optimization: before
  rounding, each is an upper bound for J, not a certified minimum, and a printed value can fall
  below J by up to half a unit in its last digit. The conclusions drawn from them follow from
  proved results, except the decrease of J in Remark 53, which rests on a root finding whose
  completeness is not certified. The lines `[ok] … J > 0 (soporte conexo)` printed by
  `python/numeric/J_conectividad.py` only check that the computed values, which are upper
  bounds, are consistent with the connectivity lemma; that J > 0 on a connected support is the
  lemma itself (Lemma 29), not a computed value.
- **Formalization.** Lean checks the logical form of statements; whether a physical or
  phenomenal premise holds is never decided by a compilation. Some analytic statements
  remain paper proofs, as their labels say.
- **Self-audit.** Q is the author's own proposal. Every definition, hypothesis and result
  that the audit uses is stated in the paper, so the audit can be checked from the paper and
  this archive alone.
- **Q's open obligations.** The original obligations of Q remain open. The descriptor Φ_Q
  and its grain γ, the original domain D_0 and the comparison relation for the degree (a ψ,
  or a substitute) are decisions that have not been taken. The conditional theorem of
  Section 2.8 states what premises would discharge some of these obligations and justifies
  none of them.

## Use of generative AI

The paper was drafted, and its Lean files and scripts were written and run, by an AI
assistant (Claude Code, by Anthropic, with Anthropic's Claude models). This was done at the
request and under the direction of the author, who is responsible for the content.

Separate agents (sessions) of the same assistant read the primary sources, checked the
Gaussian families, translated version 1.0 of the paper from its Spanish master version (the
changes of version 1.1 were written in English), formalized the
analytic results with Mathlib, and reviewed the mathematics, the citations, the scope of the
claims, the reproducibility of this archive and the formalization adversarially. The
pre-submission review that led to version 1.1 (its adversarial verification, the conditional
theorem of Section 2.8 and its Lean file, the Lean module with real-valued degrees for
Theorem 51 and the archived second check of Table 6) was also done by agents of the same
assistant. Their agreement is not an independent validation, and there has been no
independent human review. During the research the author also used another AI system in
exploratory conversations; that material was treated as unverified input, and no result of
the paper depends on it.

What is machine-checked is stated by the labels above: every [L] and [M] statement is checked
by the Lean kernel, in its logical form only, and every [S] statement by exact computation.
Version 1.0 called the second check of the four-unit networks independent and said that it
was not archived; it is not independent, and it is now archived (`CHANGES.md`).

## How to cite

Toranzo Portela, Á. J. (2026). *A Formal Audit of a Categorical Unification of
Consciousness Theories: Structural Proxies, Formal Obstructions and a Positive Route*
(version 1.1). Preprint and verification archive, Zenodo. https://doi.org/10.5281/zenodo.24349943

The DOI above is the concept DOI, which always resolves to the latest version. Version 1.1
receives its own DOI when it is released; version 1.0 has the DOI
https://doi.org/10.5281/zenodo.24349944.

## License

This archive is distributed under the Creative Commons Attribution 4.0 International
license (CC BY 4.0); see `LICENSE`. `paper/source/compositionalityarticle.cls` is the
official class of the journal Compositionality, included unmodified, and keeps its own
license, the LaTeX Project Public License 1.3c.

---

## Resumen en español

El artículo define un marco candidato, Q, propuesto por su autor, que pretende unificar
categóricamente varias teorías de la consciencia (IIT, GNWT y la teoría del esquema de
atención) y marcos generales aplicados a ella (el principio de energía libre y el
darwinismo cuántico), y lo audita formalmente. Trabaja con sustitutos estructurales de esas
teorías, no con las teorías mismas: J no es el Φ de IIT 3.0, y el hub de difusión, leído en
el grafo no dirigido del soporte, no modela la ignición ni la difusión dinámica de GNWT. El
caso de prueba es la obligación de suficiencia de unidad S_u de Q, y la auditoría no cambia
el descriptor, el dominio ni el significado de Q. Toda definición, hipótesis y resultado que
usa está enunciado en el propio artículo.

Tiene tres actos:

1. **Delimitación negativa.** Comprende:
   - la tesis débil, que vale pero sale barata, porque se cumple para cualquier familia de
     invariantes;
   - la tesis fuerte, falsa para los puentes de presencia de tipo IIT y GNWT, que discrepan
     exactamente en la banda (vacía para n ≤ 3, y con P_n y C_n para todo n ≥ 4);
   - el criterio exacto con que las premisas de factorización implican S_u, que dice qué
     relaciones bastarían, no que haya una disponible;
   - los principios examinados, que no cierran S_u sin presuponerla, igualar solo
     realizaciones isomorfas, colapsar el grado, cambiar su significado o cambiar el
     dominio;
   - SEG, que es S_u no degenerada reescrita en forma contrastable;
   - un teorema condicional (teorema 26, sección 2.8, nuevo en la versión 1.1) que enuncia
     qué premisas descargarían las cinco obligaciones de suficiencia, la cláusula de orden B y
     la condición de descenso O, sin establecer ninguna.
2. **Laboratorio gaussiano.** Es exacto con dos unidades y numérico con cuatro. Ilustra, para
   la lectura no dirigida del hub, dónde conmutan y dónde se rompen los puentes (en las redes
   de cuatro unidades los valores calculados de J son cotas superiores, y el patrón se sigue
   del lema de conectividad y de las comprobaciones de Lean), y muestra de forma exacta que la
   cota inferior del corte mínimo se alcanza. La aditividad de la información predictiva se
   separa del monoide de producto nulo. Elegir el estado de sorpresa mínima es trivial sobre
   leyes y descarta casi todas las realizaciones sobre estados: la moda tiene probabilidad
   cero.
3. **Vía positiva.** De las reformulaciones examinadas, solo la monotonía bajo
   intervenciones resiste el colapso. No es S_u ni una obligación de Q, sino un
   debilitamiento declarado de su cláusula de orden, y no se ha mostrado que sea la única.
   Su frontera exacta (teorema 51) es la conexidad fuerte del digrafo de intervenciones; la
   función que separa dos componentes es una construcción matemática, que no se identifica
   con el grado de unidad u de Q. En la banda
   puede instanciarse tomando J en lugar del descriptor de Q, cosa que no se justifica: con
   al menos dos unidades, J crece estrictamente bajo escalado uniforme de una dinámica de
   soporte conexo, o al escalar acoplamientos de soporte conexo con autoacoplamiento escalar
   fijo (comprobado en Lean con Mathlib). Numéricamente, J puede decrecer si el autoacoplamiento
   fijo no es escalar.

Q no queda demostrada ni refutada.

Para verificarlo todo, desde la raíz del archivo: `bash verify_all.sh` (o `make verify`).
El guion comprueba primero las sumas SHA-256 de todos los ficheros y después ejecuta
`lean/verify_lean.sh` (siete ficheros de Lean sin Mathlib), `python/verify_python.sh` (doce
guiones) y `lean-mathlib/verify_mathlib.sh` (ocho módulos con Mathlib); su
última línea debe ser `ALL CHECKS PASSED`. Con `SKIP_MATHLIB=1` se omite la parte de
Mathlib, que descarga cerca de 1 GB y necesita unos 7 GB de disco; el resumen lo indica y
la última línea es entonces `ALL CHECKS THAT RAN PASSED (skipped: Lean-with-Mathlib)`.
La tabla 1 del artículo da la etiqueta de cada resultado principal y el teorema de Lean o
el guion que lo comprueba. Las etiquetas de estatus son [L] Lean sin Mathlib, [M] Lean con
Mathlib, [A] papel, [S] cálculo exacto y [N] numérico; un valor de J obtenido por
optimización local es, antes de redondearlo, una cota superior de J, y un valor impreso puede
quedar por debajo de J hasta media unidad de su última cifra. El lema de conectividad de J,
el emparedado del corte mínimo, la proposición de escalado y la frontera exacta de la
monotonía bajo intervenciones con grados reales están comprobados en Lean con Mathlib. La
versión 1.0 llamaba independiente a la segunda comprobación de las redes de cuatro unidades y
decía que no estaba archivada: no es independiente, porque comparte con
`pistas_numerico.py` el objetivo, los datos, el predictor inicial y código, y ahora está
archivada (`python/numeric/segundo_optimizador.py`). Los cambios respecto de la versión 1.0
están en `CHANGES.md`. Licencia: CC BY 4.0, salvo `paper/source/compositionalityarticle.cls`,
que conserva la LPPL 1.3c. DOI de todas las versiones (DOI conceptual, que resuelve a la
última): 10.5281/zenodo.24349943; DOI de la versión 1.0: 10.5281/zenodo.24349944; el DOI de
la versión 1.1 se asigna al publicarla.
