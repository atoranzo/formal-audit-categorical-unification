import QAuditAnalytic.LemmaJ

/-!
# Audit of `QAuditAnalytic/LemmaJ.lean` (non-vacuity and sharpness checks)

Written separately from the other modules, which it does not modify.

1. `J_ex_eq`: on the concrete two-unit system of `LemmaJExample` (`A₀₁ = 1/2`, `E = 1`,
   `P = diag (5/4, 1)`), `J` takes the exact value `½ log (5/4) > 0`.  So `J` is not degenerate
   (not identically `0`, not a junk `sInf`), and the lower bound of the sandwich is attained there.
2. `lamMax_Pex`, `lamMin_one`, `lamMax_one`: the eigenvalue constants of `Core.lean` evaluate to
   the true extreme eigenvalues on this example, and the *eigenvalue* version `sandwich`
   (not only the Loewner-bound version) applies and gives `½ log (5/4) ≤ J ≤ 5/32`.
-/

open Matrix

namespace QAudit.Audit

open QAudit QAudit.LemmaJExample

theorem det_Pex : det Pex = 5 / 4 := by
  rw [Pex, det_diagonal, Fin.prod_univ_two]
  norm_num

/-- The objective at `B = 0` equals `½ log (5/4)` (uses only the stationarity equation). -/
theorem objective_zero_ex : objective 1 Pex Aex 0 = 1 / 2 * Real.log (5 / 4) := by
  unfold objective
  rw [sub_zero, add_comm, ← Pex_stationary, det_Pex, det_one, div_one]

/-- **Exact value**: `J = ½ log (5/4)` on the concrete system (so `J > 0`, and the lower bound
`½ log (1 + w_min/κ_E)` of the sandwich is attained). -/
theorem J_ex_eq : J 1 Pex Aex = 1 / 2 * Real.log (5 / 4) := by
  apply le_antisymm
  · calc J 1 Pex Aex
        ≤ Jcut 1 Pex Aex ({⟨0, by omega⟩} : Finset (Fin 2)) :=
          J_le_Jcut (E := 1) (P := Pex) (A := Aex) ⟨_, isBipartition_singleton_zero (le_refl 2)⟩
      _ ≤ objective 1 Pex Aex 0 := Jcut_le PosDef.one Pex_posDef.posSemidef (zero_mem_Bpi _)
      _ = _ := objective_zero_ex
  · have h1 : ((1 : Matrix (Fin 2) (Fin 2) ℝ) - (1 : ℝ) • 1).PosSemidef := by
      rw [one_smul, sub_self]; exact PosSemidef.zero
    have h2 : ((1 : ℝ) • 1 - (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef := by
      rw [one_smul, sub_self]; exact PosSemidef.zero
    have hl := sandwich_lower (le_refl 2) PosDef.one Pex_posDef Pex_stationary one_pos h1 h2
    rw [wmin_Aex] at hl
    convert hl using 3; norm_num

theorem J_ex_pos : 0 < J 1 Pex Aex := by
  rw [J_ex_eq]
  have : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  positivity

/-! ### The eigenvalue constants are the true extreme eigenvalues on the example -/

theorem lamMax_Pex : lamMax Pex_posDef.1 = 5 / 4 := by
  have h := lamMax_isGreatest_spectrum Pex_posDef.1
  have hs : spectrum ℝ Pex = Set.range ![(5 / 4 : ℝ), 1] := by
    rw [Pex, spectrum_diagonal]
  rw [hs] at h
  have h2 : IsGreatest (Set.range ![(5 / 4 : ℝ), 1]) (5 / 4) := by
    refine ⟨⟨0, rfl⟩, ?_⟩
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> norm_num
  exact h.unique h2

theorem lamMin_Pex : lamMin Pex_posDef.1 = 1 := by
  have h := lamMin_isLeast_spectrum Pex_posDef.1
  have hs : spectrum ℝ Pex = Set.range ![(5 / 4 : ℝ), 1] := by
    rw [Pex, spectrum_diagonal]
  rw [hs] at h
  have h2 : IsLeast (Set.range ![(5 / 4 : ℝ), 1]) 1 := by
    refine ⟨⟨1, rfl⟩, ?_⟩
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> norm_num
  exact h.unique h2

theorem lamMin_one : lamMin (PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef).1 = 1 := by
  have h := lamMin_isLeast_spectrum (PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef).1
  rw [spectrum.one_eq] at h
  exact h.unique isLeast_singleton

theorem lamMax_one : lamMax (PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef).1 = 1 := by
  have h := lamMax_isGreatest_spectrum (PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef).1
  rw [spectrum.one_eq] at h
  exact h.unique isGreatest_singleton

/-- The **eigenvalue** version of the sandwich (theorem `sandwich`, the paper's exact form)
applies to the example and evaluates to `½ log (1 + 1/4) ≤ J ≤ ½ · (5/4) · (1/4)`. -/
theorem sandwich_ex :
    1 / 2 * Real.log (1 + 1 / 4 / (1 / 1)) ≤ J 1 Pex Aex ∧
      J 1 Pex Aex ≤ 1 / 2 * (5 / 4 / 1) * (1 / 4) := by
  have h := sandwich (le_refl 2) PosDef.one Pex_posDef Pex_stationary
  rw [lamMax_one, lamMin_one, lamMax_Pex, wmin_Aex] at h
  exact h

/-- Sanity: the two bounds are consistent with the exact value, and the lower one is attained. -/
example : 1 / 2 * Real.log (1 + 1 / 4 / (1 / 1)) = J 1 Pex Aex := by
  rw [J_ex_eq]; norm_num

end QAudit.Audit

#print axioms QAudit.Audit.J_ex_eq
#print axioms QAudit.Audit.J_ex_pos
#print axioms QAudit.Audit.lamMax_Pex
#print axioms QAudit.Audit.lamMin_one
#print axioms QAudit.Audit.sandwich_ex
