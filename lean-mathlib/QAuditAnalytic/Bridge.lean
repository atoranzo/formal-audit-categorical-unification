import QAuditAnalytic.LemmaJ
import QAuditAnalytic.Scaling

/-!
# Audit: the two formalizations define the same `J`

Written separately from the other modules, which it does not modify.

`QAuditAnalytic/LemmaJ.lean` (namespace `QAudit`) and `QAuditAnalytic/Scaling.lean` (namespace
`QAuditScaling`) were written independently and each defines its own `𝔅_π`, objective, inner
infimum, `J`, support graph and `w_min`.  The paper has one `J`.  This file proves that the two
definitions agree (for `E ≻ 0`, `P ⪰ 0`), so the results of both files are about the same
functional, and combines them:

* `J_eq`, `supportGraph_eq`, `wmin_eq`: the definitions coincide;
* `Jt_pos_of_connected`: Lemma J (from `LemmaJ.lean`) along the scaling path of `Scaling.lean`;
* `sandwich_along_scaling`: the min-cut sandwich (eigenvalue form) holds for `J(tA, E)` on the
  whole summability domain, with the stationary covariance built as a series (`Pt`), i.e. the
  "P given as data" hypothesis of `LemmaJ.lean` is discharged there by `Pt_posDef`/`Pt_lyap`.
-/

open Matrix

namespace QAuditBridge

variable {n : ℕ}

theorem crosses_iff {S : Finset (Fin n)} {i j : Fin n} :
    QAudit.Crosses S i j ↔ ¬ (i ∈ S ↔ j ∈ S) := by
  unfold QAudit.Crosses; tauto

theorem Bpi_eq (S : Finset (Fin n)) : QAudit.Bpi S = QAuditScaling.Bpi S := by
  ext B
  simp only [QAudit.Bpi, QAuditScaling.Bpi, Set.mem_setOf_eq, crosses_iff]

theorem objective_eq {E P A : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hP : P.PosSemidef) :
    QAudit.objective E P A = fun B => QAuditScaling.fval E P A B / 2 := by
  funext B
  unfold QAudit.objective QAuditScaling.fval
  rw [Real.log_div (QAudit.det_add_pos hE (QAudit.posSemidef_residual hP _)).ne' hE.det_pos.ne']
  ring

theorem Jcut_eq {E P A : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hP : P.PosSemidef)
    (S : Finset (Fin n)) : QAudit.Jcut E P A S = QAuditScaling.JS E P A S := by
  unfold QAudit.Jcut QAuditScaling.JS
  rw [Bpi_eq, objective_eq hE hP]

/-- **The two `J`s agree.** -/
theorem J_eq {E P A : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hP : P.PosSemidef) :
    QAudit.J E P A = QAuditScaling.J E P A := by
  unfold QAudit.J QAuditScaling.J
  simp only [Jcut_eq hE hP]
  rfl

theorem supportGraph_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    QAudit.supportGraph A = QAuditScaling.supportGraph A := by
  ext i j
  simp only [QAudit.supportGraph_adj, QAuditScaling.supportGraph, SimpleGraph.fromRel_adj]

theorem cutWeight_eq (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    QAudit.cutWeight A S = QAuditScaling.cutWeight A S := by
  unfold QAudit.cutWeight QAuditScaling.cutWeight QAudit.Across
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  by_cases h : QAudit.Crosses S i j
  · rw [if_pos h, if_neg (crosses_iff.mp h)]
  · have h' : (i ∈ S ↔ j ∈ S) := not_not.mp (mt crosses_iff.mpr h)
    rw [if_neg h, if_pos h']
    ring

theorem wmin_eq (A : Matrix (Fin n) (Fin n) ℝ) : QAudit.wmin A = QAuditScaling.wmin A := by
  unfold QAudit.wmin QAuditScaling.wmin
  simp only [cutWeight_eq]
  rfl

/-- Lemma J along the scaling path: for connected support, `J(tA, E) > 0` for every `t > 0` in
the summability domain (in particular on the paper range `[0, 1/spr(A))`). -/
theorem Jt_pos_of_connected (hn : 2 ≤ n) {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    (hA : (QAudit.supportGraph A).Connected) {t : ℝ} (ht : 0 < t)
    (hs : QAuditScaling.SummableAt A E t) : 0 < QAuditScaling.Jt A E t := by
  have hP := QAuditScaling.Pt_posDef hE ht.le hs
  unfold QAuditScaling.Jt
  rw [← J_eq hE hP.posSemidef, QAudit.lemmaJ hn hE hP, supportGraph_eq,
    QAuditScaling.supportGraph_smul _ ht.ne', ← supportGraph_eq]
  exact hA

/-- The min-cut sandwich (eigenvalue form, theorem `QAudit.sandwich`) along the scaling path,
with the covariance constructed as the series `P_t` (no covariance assumed as data). -/
theorem sandwich_along_scaling (hn : 2 ≤ n) {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    {t : ℝ} (ht : t ∈ QAuditScaling.Dom A E) :
    1 / 2 * Real.log (1 + t ^ 2 * QAudit.wmin A / (QAudit.lamMax hE.1 / QAudit.lamMin hE.1)) ≤
        QAuditScaling.Jt A E t ∧
      QAuditScaling.Jt A E t ≤
        1 / 2 * (QAudit.lamMax (QAuditScaling.Pt_posDef hE ht.1 ht.2).1 / QAudit.lamMin hE.1) *
          (t ^ 2 * QAudit.wmin A) := by
  have hP := QAuditScaling.Pt_posDef hE ht.1 ht.2
  have hstat := QAuditScaling.Pt_lyap ht.2
  have h := QAudit.sandwich hn hE hP hstat
  have hw : QAudit.wmin (t • A) = t ^ 2 * QAudit.wmin A := by
    rw [wmin_eq, wmin_eq, QAuditScaling.wmin_smul]
  rw [J_eq hE hP.posSemidef, hw] at h
  exact h

/-- Under the paper's standing assumption `spr(A) < 1`, the stationary covariance exists as the
series `∑ A^j E (A^j)ᵀ` (convergence via Gelfand's formula, `serSummable_of_spr_lt_one`), and it
satisfies the hypotheses taken as data in `LemmaJ.lean` (`P ≻ 0`, `P = A P Aᵀ + E`). -/
theorem stationary_of_spr {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    (hspr : QAuditScaling.spr A < 1) :
    (QAuditScaling.Pser A E).PosDef ∧
      QAuditScaling.Pser A E = A * QAuditScaling.Pser A E * Aᵀ + E :=
  ⟨QAuditScaling.Pser_posDef hE (QAuditScaling.serSummable_of_spr_lt_one E hspr),
    QAuditScaling.Pser_lyap (QAuditScaling.serSummable_of_spr_lt_one E hspr)⟩

/-- Lemma J with the covariance constructed (not assumed): any `A` with `spr(A) < 1`. -/
theorem lemmaJ_spr (hn : 2 ≤ n) {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    (hspr : QAuditScaling.spr A < 1) :
    0 < QAudit.J E (QAuditScaling.Pser A E) A ↔ (QAudit.supportGraph A).Connected :=
  QAudit.lemmaJ_stationary hn hE (stationary_of_spr hE hspr).1 (stationary_of_spr hE hspr).2

/-- The min-cut sandwich (eigenvalue form) with the covariance constructed as a series. -/
theorem sandwich_spr (hn : 2 ≤ n) {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    (hspr : QAuditScaling.spr A < 1) :
    1 / 2 * Real.log (1 + QAudit.wmin A / (QAudit.lamMax hE.1 / QAudit.lamMin hE.1)) ≤
        QAudit.J E (QAuditScaling.Pser A E) A ∧
      QAudit.J E (QAuditScaling.Pser A E) A ≤
        1 / 2 * (QAudit.lamMax (stationary_of_spr hE hspr).1.1 / QAudit.lamMin hE.1) *
          QAudit.wmin A :=
  QAudit.sandwich hn hE (stationary_of_spr hE hspr).1 (stationary_of_spr hE hspr).2

/-- The identification used in the paper (`D_weak_unification.tex`): `J > 0 ↔ w_min > 0`,
a direct consequence of the formal sandwich. -/
theorem J_pos_iff_wmin_pos (hn : 2 ≤ n) {E P A : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    (hP : P.PosDef) (hstat : P = A * P * Aᵀ + E) :
    0 < QAudit.J E P A ↔ 0 < QAudit.wmin A := by
  obtain ⟨hl, hu⟩ := QAudit.sandwich hn hE hP hstat
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have he1 := QAudit.lamMin_pos hE
  have he2 : 0 < QAudit.lamMax hE.1 := by
    obtain ⟨i, -⟩ := QAudit.exists_eigenvalue_eq_lamMax hE.1
    exact lt_of_lt_of_le (hE.eigenvalues_pos i) (QAudit.le_lamMax hE.1 i)
  have hw0 := QAudit.wmin_nonneg hn A
  constructor
  · intro hJ
    by_contra hw
    have h0 : QAudit.wmin A = 0 := le_antisymm (not_lt.mp hw) hw0
    rw [h0, mul_zero] at hu
    linarith
  · intro hw
    have hq : 0 < QAudit.wmin A / (QAudit.lamMax hE.1 / QAudit.lamMin hE.1) := by positivity
    have := Real.log_pos (by linarith : 1 < 1 + QAudit.wmin A /
      (QAudit.lamMax hE.1 / QAudit.lamMin hE.1))
    linarith

end QAuditBridge

#print axioms QAuditBridge.J_eq
#print axioms QAuditBridge.supportGraph_eq
#print axioms QAuditBridge.wmin_eq
#print axioms QAuditBridge.Jt_pos_of_connected
#print axioms QAuditBridge.sandwich_along_scaling
#print axioms QAuditBridge.stationary_of_spr
#print axioms QAuditBridge.lemmaJ_spr
#print axioms QAuditBridge.sandwich_spr
#print axioms QAuditBridge.J_pos_iff_wmin_pos
