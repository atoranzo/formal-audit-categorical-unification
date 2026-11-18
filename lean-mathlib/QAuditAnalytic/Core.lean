import Mathlib

/-!
# Shared matrix inequalities for the Gaussian residual functional `J`

All matrices are real `n × n` matrices, `Matrix (Fin n) (Fin n) ℝ`.  The Loewner order is
written explicitly with `PosSemidef` of differences: `e • 1 ≤ E` is `(E - e • 1).PosSemidef`
and `E ≤ e • 1` is `(e • 1 - E).PosSemidef`.

Main results (used in `QAuditAnalytic/LemmaJ.lean`):

* `one_add_trace_le_det_one_add` : `1 + tr X ≤ det (1 + X)` for `X ⪰ 0`;
* `log_det_one_add_le_trace` : `log det (1 + X) ≤ tr X` for `X ⪰ 0`;
* `exists_whitening` : `E ≻ 0`, `M ⪰ 0` give `X = E^{-1/2} M E^{-1/2} ⪰ 0` with
  `det (E + M) = det E · det (1 + X)`, `tr X = tr (E⁻¹ M)`, `tr (E X) = tr M`;
* `det_mul_one_add_trace_le` : `det E · (1 + tr (E⁻¹ M)) ≤ det (E + M)`;
* `log_det_add_sub_le` : `log det (E + M) - log det E ≤ tr (E⁻¹ M)`;
* `trace_le_mul_trace_inv_mul`, `mul_trace_inv_mul_le_trace` : under `e₁ • 1 ≤ E ≤ e₂ • 1`,
  `e₁ · tr (E⁻¹ M) ≤ tr M ≤ e₂ · tr (E⁻¹ M)`;
* `trace_mul_mul_transpose_ge`, `trace_mul_mul_transpose_le` : under `p₁ • 1 ≤ P ≤ p₂ • 1`,
  `p₁ ‖C‖_F² ≤ tr (C P Cᵀ) ≤ p₂ ‖C‖_F²`;
* `lamMin`, `lamMax` (smallest / largest eigenvalue) and the Loewner bounds
  `λ_min(X) • 1 ≤ X ≤ λ_max(X) • 1`.
-/

open Matrix
open scoped MatrixOrder

namespace QAudit

variable {n : ℕ}

/-- A positive definite matrix has a positive definite square root (`CFC.sqrt`). -/
theorem exists_posDef_sqrt {E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ, S.PosDef ∧ S * S = E :=
  ⟨CFC.sqrt E, hE.posDef_sqrt, CFC.sqrt_mul_sqrt_self E hE.posSemidef.nonneg⟩

/-- A positive semidefinite matrix has a positive semidefinite square root. -/
theorem exists_psd_sqrt {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) :
    ∃ T : Matrix (Fin n) (Fin n) ℝ, T.PosSemidef ∧ T * T = M :=
  ⟨CFC.sqrt M, nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M),
    CFC.sqrt_mul_sqrt_self M hM.nonneg⟩

/-- The trace of a product of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg {Q M : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef)
    (hM : M.PosSemidef) : 0 ≤ trace (Q * M) := by
  obtain ⟨T, hT, rfl⟩ := exists_psd_sqrt hM
  have h1 : trace (Q * (T * T)) = trace (T * Q * T) := by
    rw [← Matrix.mul_assoc, trace_mul_cycle]
  have h2 : (T * Q * T).PosSemidef := by
    have := hQ.mul_mul_conjTranspose_same T
    rwa [hT.isHermitian.eq] at this
  rw [h1]
  exact h2.trace_nonneg

/-- `1 + ∑ dᵢ ≤ ∏ (1 + dᵢ)` for nonnegative `dᵢ`. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 ≤ d i) : 1 + ∑ i ∈ s, d i ≤ ∏ i ∈ s, (1 + d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hs : ∀ i ∈ s, 0 ≤ d i := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have ih := ih hs
    have hda := hd a (Finset.mem_insert_self a s)
    have hsum : 0 ≤ ∑ i ∈ s, d i := Finset.sum_nonneg hs
    nlinarith

theorem unitary_mul_star {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hX.eigenvectorUnitary.2

theorem star_mul_unitary {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2

/-- Spectral form of `X - c • 1`: `U · diag (λᵢ - c) · Uᴴ`. -/
theorem sub_smul_one_eq {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) (c : ℝ) :
    X - c • 1 = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      diagonal (fun i => hX.eigenvalues i - c) *
      star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
  have hU := unitary_mul_star hX
  have hspec := hX.spectral_theorem
  have hd : diagonal (fun i => hX.eigenvalues i - c) =
      diagonal (RCLike.ofReal ∘ hX.eigenvalues) - c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, ← hspec, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hU]

/-- `det (X - c • 1) = ∏ (λᵢ - c)`. -/
theorem det_sub_smul_one {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) (c : ℝ) :
    det (X - c • 1) = ∏ i, (hX.eigenvalues i - c) := by
  rw [sub_smul_one_eq hX c, det_mul, det_mul,
    mul_comm (det (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)), mul_assoc, ← det_mul,
    unitary_mul_star hX, det_one, mul_one, det_diagonal]

/-- `det (1 + X) = ∏ (1 + λᵢ)`. -/
theorem det_one_add {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    det (1 + X) = ∏ i, (1 + hX.eigenvalues i) := by
  have h : (1 : Matrix (Fin n) (Fin n) ℝ) + X = X - (-1 : ℝ) • 1 := by
    rw [neg_smul, one_smul, sub_neg_eq_add, add_comm]
  rw [h, det_sub_smul_one hX]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  ring

/-- `tr X = ∑ λᵢ`. -/
theorem trace_eq_sum_eig {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    trace X = ∑ i, hX.eigenvalues i := by
  rw [hX.trace_eq_sum_eigenvalues]
  simp

/-- `1 + tr X ≤ det (1 + X)` for PSD `X`. -/
theorem one_add_trace_le_det_one_add {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) :
    1 + trace X ≤ det (1 + X) := by
  rw [det_one_add hX.1, trace_eq_sum_eig hX.1]
  exact one_add_sum_le_prod_one_add _ _ (fun i _ => hX.eigenvalues_nonneg i)

/-- `log det (1 + X) ≤ tr X` for PSD `X`. -/
theorem log_det_one_add_le_trace {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) :
    Real.log (det (1 + X)) ≤ trace X := by
  have hpos : ∀ i, 0 < 1 + hX.1.eigenvalues i := fun i => by
    have := hX.eigenvalues_nonneg i; linarith
  rw [det_one_add hX.1, trace_eq_sum_eig hX.1,
    Real.log_prod _ _ (fun i _ => (hpos i).ne')]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have := Real.log_le_sub_one_of_pos (hpos i)
  linarith

/-- Whitening: for `E` positive definite and `M` positive semidefinite there is a positive
semidefinite `X` (namely `E^{-1/2} M E^{-1/2}`) with `det (E + M) = det E * det (1 + X)`,
`tr X = tr (E⁻¹ M)` and `tr (E X) = tr M`. -/
theorem exists_whitening {E M : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hM : M.PosSemidef) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ, X.PosSemidef ∧ det (E + M) = det E * det (1 + X) ∧
      trace X = trace (E⁻¹ * M) ∧ trace (E * X) = trace M := by
  obtain ⟨S, hS, hSS⟩ := exists_posDef_sqrt hE
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have h1 : S * S⁻¹ = 1 := mul_nonsing_inv S hSu
  have h2 : S⁻¹ * S = 1 := nonsing_inv_mul S hSu
  have hSiH : (S⁻¹)ᴴ = S⁻¹ := hS.inv.isHermitian.eq
  refine ⟨S⁻¹ * M * S⁻¹, ?_, ?_, ?_, ?_⟩
  · have := hM.conjTranspose_mul_mul_same S⁻¹
    rwa [hSiH] at this
  · have hEM : E + M = S * (1 + S⁻¹ * M * S⁻¹) * S := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [hEM, det_mul, det_mul, ← hSS, det_mul]
    ring
  · rw [trace_mul_cycle, ← hSS, Matrix.mul_inv_rev]
  · rw [← hSS]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S S⁻¹, h1, Matrix.one_mul, trace_mul_comm, Matrix.mul_assoc, h2,
      Matrix.mul_one]


section consequences

variable {E M : Matrix (Fin n) (Fin n) ℝ}

theorem trace_inv_mul_nonneg (hE : E.PosDef) (hM : M.PosSemidef) : 0 ≤ trace (E⁻¹ * M) := by
  obtain ⟨X, hX, -, hXt, -⟩ := exists_whitening hE hM
  rw [← hXt]; exact hX.trace_nonneg

/-- `det E · (1 + tr (E⁻¹ M)) ≤ det (E + M)`. -/
theorem det_mul_one_add_trace_le (hE : E.PosDef) (hM : M.PosSemidef) :
    det E * (1 + trace (E⁻¹ * M)) ≤ det (E + M) := by
  obtain ⟨X, hX, hdet, hXt, -⟩ := exists_whitening hE hM
  rw [hdet, ← hXt]
  exact mul_le_mul_of_nonneg_left (one_add_trace_le_det_one_add hX) hE.det_pos.le

theorem det_add_pos (hE : E.PosDef) (hM : M.PosSemidef) : 0 < det (E + M) := by
  have h1 := det_mul_one_add_trace_le hE hM
  have h2 := trace_inv_mul_nonneg hE hM
  have h3 := hE.det_pos
  nlinarith

/-- `log det (E + M) - log det E ≤ tr (E⁻¹ M)`. -/
theorem log_det_add_sub_le (hE : E.PosDef) (hM : M.PosSemidef) :
    Real.log (det (E + M)) - Real.log (det E) ≤ trace (E⁻¹ * M) := by
  obtain ⟨X, hX, hdet, hXt, -⟩ := exists_whitening hE hM
  have hX1 : 0 < det (1 + X) := by
    have := one_add_trace_le_det_one_add hX
    have := hX.trace_nonneg
    linarith
  rw [hdet, Real.log_mul hE.det_pos.ne' hX1.ne', ← hXt]
  have := log_det_one_add_le_trace hX
  linarith

/-- If `E ≤ e₂ • 1` then `tr M ≤ e₂ · tr (E⁻¹ M)`. -/
theorem trace_le_mul_trace_inv_mul (hE : E.PosDef) (hM : M.PosSemidef) {e₂ : ℝ}
    (hE₂ : (e₂ • 1 - E).PosSemidef) : trace M ≤ e₂ * trace (E⁻¹ * M) := by
  obtain ⟨X, hX, -, hXt, hEX⟩ := exists_whitening hE hM
  have h := trace_mul_nonneg hE₂ hX
  rw [Matrix.sub_mul, trace_sub, Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul,
    hEX, hXt] at h
  linarith

/-- If `e₁ • 1 ≤ E` then `e₁ · tr (E⁻¹ M) ≤ tr M`. -/
theorem mul_trace_inv_mul_le_trace (hE : E.PosDef) (hM : M.PosSemidef) {e₁ : ℝ}
    (hE₁ : (E - e₁ • 1).PosSemidef) : e₁ * trace (E⁻¹ * M) ≤ trace M := by
  obtain ⟨X, hX, -, hXt, hEX⟩ := exists_whitening hE hM
  have h := trace_mul_nonneg hE₁ hX
  rw [Matrix.sub_mul, trace_sub, Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul,
    hEX, hXt] at h
  linarith

end consequences

/-- The squared Frobenius norm, written as a double sum of squares. -/
theorem trace_mul_transpose_self (C : Matrix (Fin n) (Fin n) ℝ) :
    trace (C * Cᵀ) = ∑ i, ∑ j, C i j ^ 2 := by
  simp [trace, mul_apply, sq]

theorem trace_mul_mul_transpose_ge {P : Matrix (Fin n) (Fin n) ℝ} {p₁ : ℝ}
    (hP₁ : (P - p₁ • 1).PosSemidef) (C : Matrix (Fin n) (Fin n) ℝ) :
    p₁ * ∑ i, ∑ j, C i j ^ 2 ≤ trace (C * P * Cᵀ) := by
  have h := (hP₁.mul_mul_conjTranspose_same C).trace_nonneg
  rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul, trace_sub,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, trace_smul, smul_eq_mul,
    trace_mul_transpose_self] at h
  linarith

theorem trace_mul_mul_transpose_le {P : Matrix (Fin n) (Fin n) ℝ} {p₂ : ℝ}
    (hP₂ : (p₂ • 1 - P).PosSemidef) (C : Matrix (Fin n) (Fin n) ℝ) :
    trace (C * P * Cᵀ) ≤ p₂ * ∑ i, ∑ j, C i j ^ 2 := by
  have h := (hP₂.mul_mul_conjTranspose_same C).trace_nonneg
  rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul, trace_sub,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, trace_smul, smul_eq_mul,
    trace_mul_transpose_self] at h
  linarith

/-- Two-sided trace bound: under `e₁ • 1 ≤ E ≤ e₂ • 1` (`e₁, e₂ > 0`) and
`p₁ • 1 ≤ P ≤ p₂ • 1` (`P ⪰ 0`),
`(p₁/e₂) ‖C‖_F² ≤ tr (E⁻¹ C P Cᵀ) ≤ (p₂/e₁) ‖C‖_F²`. -/
theorem trace_inv_mul_residual_bounds {E P : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    (hP : P.PosSemidef) {e₁ e₂ p₁ p₂ : ℝ} (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hE₁ : (E - e₁ • 1).PosSemidef) (hE₂ : (e₂ • 1 - E).PosSemidef)
    (hP₁ : (P - p₁ • 1).PosSemidef) (hP₂ : (p₂ • 1 - P).PosSemidef)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    p₁ / e₂ * ∑ i, ∑ j, C i j ^ 2 ≤ trace (E⁻¹ * C * P * Cᵀ) ∧
      trace (E⁻¹ * C * P * Cᵀ) ≤ p₂ / e₁ * ∑ i, ∑ j, C i j ^ 2 := by
  have hM : (C * P * Cᵀ).PosSemidef := by
    have := hP.mul_mul_conjTranspose_same C
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hassoc : E⁻¹ * C * P * Cᵀ = E⁻¹ * (C * P * Cᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc]
  have h1 := trace_le_mul_trace_inv_mul hE hM hE₂
  have h2 := mul_trace_inv_mul_le_trace hE hM hE₁
  have h3 := trace_mul_mul_transpose_ge hP₁ C
  have h4 := trace_mul_mul_transpose_le hP₂ C
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ he₂]
    linarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ he₁]
    linarith

/-- Loewner bounds from eigenvalue bounds. -/
theorem posSemidef_sub_smul_one {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) {c : ℝ}
    (hc : ∀ i, c ≤ hX.eigenvalues i) : (X - c • 1).PosSemidef := by
  rw [sub_smul_one_eq hX c]
  have hD : (diagonal (fun i => hX.eigenvalues i - c)).PosSemidef :=
    PosSemidef.diagonal (fun i => by simp only [Pi.zero_apply]; linarith [hc i])
  have := hD.mul_mul_conjTranspose_same (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  rwa [← star_eq_conjTranspose] at this

theorem posSemidef_smul_one_sub {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) {c : ℝ}
    (hc : ∀ i, hX.eigenvalues i ≤ c) : (c • 1 - X).PosSemidef := by
  have h1 : c • (1 : Matrix (Fin n) (Fin n) ℝ) - X = -(X - c • 1) := (neg_sub _ _).symm
  rw [h1, sub_smul_one_eq hX c, ← Matrix.neg_mul, ← Matrix.mul_neg, diagonal_neg]
  simp only [neg_sub]
  have hD : (diagonal (fun i => c - hX.eigenvalues i)).PosSemidef :=
    PosSemidef.diagonal (fun i => by simp only [Pi.zero_apply]; linarith [hc i])
  have := hD.mul_mul_conjTranspose_same (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  rwa [← star_eq_conjTranspose] at this


/-! ### Extreme eigenvalues -/

/-- The smallest eigenvalue `λ_min` of a real symmetric matrix. -/
noncomputable def lamMin {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) : ℝ :=
  ⨅ i, hX.eigenvalues i

/-- The largest eigenvalue `λ_max` of a real symmetric matrix. -/
noncomputable def lamMax {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) : ℝ :=
  ⨆ i, hX.eigenvalues i

theorem lamMin_le {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) (i : Fin n) :
    lamMin hX ≤ hX.eigenvalues i :=
  ciInf_le (Set.finite_range _).bddBelow i

theorem le_lamMax {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) (i : Fin n) :
    hX.eigenvalues i ≤ lamMax hX :=
  le_ciSup (Set.finite_range _).bddAbove i

/-- `λ_min` is an eigenvalue (attained) when there is at least one unit. -/
theorem exists_eigenvalue_eq_lamMin [Nonempty (Fin n)] {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) : ∃ i, hX.eigenvalues i = lamMin hX :=
  exists_eq_ciInf_of_finite

/-- `λ_max` is an eigenvalue (attained) when there is at least one unit. -/
theorem exists_eigenvalue_eq_lamMax [Nonempty (Fin n)] {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) : ∃ i, hX.eigenvalues i = lamMax hX :=
  exists_eq_ciSup_of_finite

/-- `λ_min` is the least element of the (real) spectrum. -/
theorem lamMin_isLeast_spectrum [Nonempty (Fin n)] {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) : IsLeast (spectrum ℝ X) (lamMin hX) := by
  rw [hX.spectrum_real_eq_range_eigenvalues]
  obtain ⟨i, hi⟩ := exists_eigenvalue_eq_lamMin hX
  exact ⟨⟨i, hi⟩, by rintro _ ⟨j, rfl⟩; exact lamMin_le hX j⟩

/-- `λ_max` is the greatest element of the (real) spectrum. -/
theorem lamMax_isGreatest_spectrum [Nonempty (Fin n)] {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) : IsGreatest (spectrum ℝ X) (lamMax hX) := by
  rw [hX.spectrum_real_eq_range_eigenvalues]
  obtain ⟨i, hi⟩ := exists_eigenvalue_eq_lamMax hX
  exact ⟨⟨i, hi⟩, by rintro _ ⟨j, rfl⟩; exact le_lamMax hX j⟩

theorem lamMin_pos [Nonempty (Fin n)] {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosDef) :
    0 < lamMin hX.1 := by
  obtain ⟨i, hi⟩ := exists_eigenvalue_eq_lamMin hX.1
  rw [← hi]
  exact hX.eigenvalues_pos i

/-- `λ_min(X) • 1 ≤ X` in the Loewner order. -/
theorem posSemidef_sub_lamMin {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    (X - lamMin hX • 1).PosSemidef :=
  posSemidef_sub_smul_one hX (lamMin_le hX)

/-- `X ≤ λ_max(X) • 1` in the Loewner order. -/
theorem posSemidef_lamMax_sub {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    (lamMax hX • 1 - X).PosSemidef :=
  posSemidef_smul_one_sub hX (le_lamMax hX)

/-! ### Axiom audit of the shared inequalities -/

#print axioms one_add_trace_le_det_one_add
#print axioms log_det_one_add_le_trace
#print axioms exists_whitening
#print axioms det_mul_one_add_trace_le
#print axioms log_det_add_sub_le
#print axioms trace_le_mul_trace_inv_mul
#print axioms mul_trace_inv_mul_le_trace
#print axioms trace_mul_mul_transpose_ge
#print axioms trace_mul_mul_transpose_le
#print axioms trace_inv_mul_residual_bounds
#print axioms posSemidef_sub_lamMin
#print axioms posSemidef_lamMax_sub
#print axioms lamMin_isLeast_spectrum
#print axioms lamMax_isGreatest_spectrum

end QAudit
