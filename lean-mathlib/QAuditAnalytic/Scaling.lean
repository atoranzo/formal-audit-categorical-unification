import Mathlib

/-!
# Monotonicity of `J` under scaling (Proposition `prop:scaling`)

Self-contained formalization (only `import Mathlib`) of Proposition `prop:scaling` of
`G_positive_route.tex`, over real matrices `Matrix (Fin n) (Fin n) ℝ`.

## Setting
* `Bpi S` (`𝔅_π`): matrices with no coefficient crossing the bipartition `S | Sᶜ`.
* `fval E P A B = log det (E + (A-B) P (A-B)ᵀ) - log det E` (twice the paper's `f`).
* `JS E P A S = sInf {fval E P A B / 2 | B ∈ Bpi S}` (`J_π`; an infimum, attainment is the
  separate theorem `exists_minimizer`), and `J E P A = ⨅ π, JS E P A π` over the finite type
  `Bip n` of bipartitions (`S`, `Sᶜ` nonempty), i.e. the minimum over bipartitions.
  The covariance `P` is an argument.
* Part (a): `Pt A E t = ∑' j, t^(2j) • (A^j E (A^j)ᵀ)` (the stationary covariance of `tA`:
  `Pt_lyap` proves `P_t = (tA) P_t (tA)ᵀ + E`), and `Jt A E t = J E (Pt A E t) (t • A)`.
  `Dom A E = {t | 0 ≤ t ∧ SummableAt A E t}` is where the series converges.
* Part (b): `Acoup a c W = a • 1 + c • W`, `Pser M E = ∑' j, M^j E (M^j)ᵀ` (solves
  `P = M P Mᵀ + E`, `Pser_lyap`), `Jb a W E c = J E (Pser (Acoup a c W) E) (Acoup a c W)`, and
  `DomB a W E = {c | 0 ≤ c ∧ SerSummable (Acoup a c W) E}`.
* `spr M = spectralRadius ℂ (M.map (algebraMap ℝ ℂ))`, the spectral radius of a real matrix.
  `serSummable_of_spr_lt_one` (Gelfand's formula) shows `spr M < 1 ⇒` the covariance series
  converges, so the paper's ranges lie inside `Dom`/`DomB`, and `spr_smul` gives
  `spr(tA) = t · spr(A)`.

## Main results
* `Pt_mono`, `sq_smul_Pt_mono`: `t ↦ P_t` and `t ↦ t² P_t` are Loewner nondecreasing.
* `resid_incr`: equation `eq:resid-incr`, with the exact decomposition of the increment.
* `JS_eq_Rt`: the reparametrization `B = tB'` (`J_π(tA)` as an infimum of residuals `R_t(B')`).
* `exists_minimizer`: a minimizer of `f` on `𝔅_π` exists (continuity + coercivity).
* `prop_scaling_a_monotone`, `prop_scaling_a_zero`, `prop_scaling_a_strictMono` (on `Dom A E`)
  and `prop_scaling_a` (on the paper's range `t ∈ [0, 1/spr(A))`).
* `Qb_mono`: `Q(c) = c² P(c)` satisfies `Q(c₂) - Q(c₁) ⪰ (c₂-c₁)² E` (finite-difference form of
  `eq:S-identity`, via the Stein equation `Q₂-Q₁ = A₂(Q₂-Q₁)A₂ᵀ + S̃`).
* `prop_scaling_b_monotone`, `prop_scaling_b_zero`, `prop_scaling_b_strictMono` (on `DomB`) and
  `prop_scaling_b` (on the paper's `𝒞 = {c ≥ 0 : spr(aI + cW) < 1}`).
* `wmin_smul`, `wmin_Acoup`: in a fixed representative the minimum cut
  `w_min = min_π ‖A_cross(π)‖_F²` scales as `t²` (resp. `c²`); `supportGraph_smul`,
  `supportGraph_Acoup`: for `t, c ≠ 0` the support is that of `A` (resp. `W`).

## Non-vacuity
* Two examples (one per part) with `n = 2`, connected support and every `t ≥ 0`, `c ≥ 0` in the
  domain, so the strict statements apply on `[0, ∞)`.
* `spr_lt_top`, `spr_range_contains`, `sprB_range_contains`: the paper's ranges
  `{t ≥ 0 : t · spr(A) < 1}` and `{c ≥ 0 : spr(aI + cW) < 1}` (for `|a| < 1`) contain an
  interval `[0, ε)` with `ε > 0`, for every `A`, `W`.

## Conventions
* `JS` uses `sInf` of a set shown nonempty (`0 ∈ 𝔅_π`) and bounded below by `0` (`JS_le`,
  `le_JS`, `JS_nonneg`); its attainment is `exists_minimizer`.
* For `n ≤ 1` there are no bipartitions and Lean's `⨅` over an empty type is `0` (the paper uses
  `+∞`); every strictness statement assumes `n ≥ 2`, as the proposition does.
-/

open Matrix

namespace QAuditScaling

variable {n : ℕ}

/-- Over `ℝ` the conjugate transpose is the transpose. -/
lemma ct (B : Matrix (Fin n) (Fin n) ℝ) : Bᴴ = Bᵀ := conjTranspose_eq_transpose_of_trivial B

lemma psd_congr {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) (C : Matrix (Fin n) (Fin n) ℝ) :
    (C * X * Cᵀ).PosSemidef := by
  simpa [ct] using hX.mul_mul_conjTranspose_same C

/-- `1 + ∑ x ≤ ∏ (1 + x)` for nonnegative reals. -/
lemma one_add_sum_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h2 := hf a (Finset.mem_insert_self a s)
    have h3 : 0 ≤ ∑ i ∈ s, f i :=
      Finset.sum_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    nlinarith

/-- `det (1 + N) ≥ 1 + tr N` for `N ⪰ 0`. -/
lemma one_add_trace_le_det {N : Matrix (Fin n) (Fin n) ℝ} (hN : N.PosSemidef) :
    1 + N.trace ≤ det (1 + N) := by
  classical
  have hH := hN.isHermitian
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUdef
  have hU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hspec : N = U * diagonal hH.eigenvalues * star U := by
    have := hH.spectral_theorem
    simpa [RCLike.ofReal_real_eq_id, Function.id_comp] using this
  have hd : diagonal (fun i => 1 + hH.eigenvalues i) = 1 + diagonal hH.eigenvalues := by
    ext i j
    by_cases h : i = j <;> simp [h]
  have h1 : 1 + N = U * diagonal (fun i => 1 + hH.eigenvalues i) * star U := by
    rw [hd, mul_add, add_mul, mul_one, hU, ← hspec]
  have hdetU : det U * det (star U) = 1 := by rw [← det_mul, hU, det_one]
  have hdet : det (1 + N) = ∏ i, (1 + hH.eigenvalues i) := by
    rw [h1, det_mul, det_mul, det_diagonal]
    calc det U * (∏ i, (1 + hH.eigenvalues i)) * det (star U)
        = (det U * det (star U)) * ∏ i, (1 + hH.eigenvalues i) := by ring
      _ = _ := by rw [hdetU, one_mul]
  have htr : N.trace = ∑ i, hH.eigenvalues i := by
    simpa using hH.trace_eq_sum_eigenvalues
  rw [hdet, htr]
  exact one_add_sum_le_prod _ _ (fun i _ => hN.eigenvalues_nonneg i)

lemma trace_pos_of_ne_zero {N : Matrix (Fin n) (Fin n) ℝ} (hN : N.PosSemidef) (h : N ≠ 0) :
    0 < N.trace :=
  lt_of_le_of_ne hN.trace_nonneg (fun h' => h (hN.trace_eq_zero_iff.mp h'.symm))

/-- Every positive semidefinite real matrix factors as `Bᴴ B` (from the spectral theorem). -/
lemma exists_factor {E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosSemidef) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, E = Bᴴ * B := by
  classical
  have hH := hE.isHermitian
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hspec : E = U * diagonal hH.eigenvalues * star U := by
    simpa [Function.id_comp] using hH.spectral_theorem
  set d : Fin n → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  have hd : diagonal d * diagonal d = diagonal hH.eigenvalues := by
    rw [diagonal_mul_diagonal]
    congr 1; funext i
    exact Real.mul_self_sqrt (hE.eigenvalues_nonneg i)
  refine ⟨diagonal d * star U, ?_⟩
  rw [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
    diagonal_conjTranspose, star_trivial, hspec, star_eq_conjTranspose, ← hd]
  simp only [Matrix.mul_assoc]

/-- Loewner monotonicity of `det` (and strictness for a nonzero increment). -/
lemma det_add_psd {E D : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hD : D.PosSemidef) :
    det E ≤ det (E + D) ∧ (D ≠ 0 → det E < det (E + D)) := by
  classical
  obtain ⟨B, hB⟩ := exists_factor hE.posSemidef
  have hdetE : det E = det B * det B := by
    rw [hB, det_mul, det_conjTranspose]; simp
  have hdetEpos := hE.det_pos
  have hBdet : IsUnit (det B) := by
    rw [isUnit_iff_ne_zero]; intro h0; rw [hdetE, h0, zero_mul] at hdetEpos
    exact lt_irrefl _ hdetEpos
  set Bi := B⁻¹ with hBi
  have h2 : Bi * B = 1 := nonsing_inv_mul B hBdet
  set N := Biᴴ * D * Bi with hN
  have hNpsd : N.PosSemidef := hD.conjTranspose_mul_mul_same Bi
  have hBB : Bᴴ * Biᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have hED : E + D = Bᴴ * (1 + N) * B := by
    rw [hB, mul_add, add_mul, mul_one]
    congr 1
    calc D = (Bᴴ * Biᴴ) * D * (Bi * B) := by rw [hBB, h2, one_mul, mul_one]
      _ = Bᴴ * (Biᴴ * D * Bi) * B := by simp only [Matrix.mul_assoc]
  have hdet : det (E + D) = det E * det (1 + N) := by
    rw [hED, det_mul, det_mul, hB, det_mul]; ring
  have hge := one_add_trace_le_det hNpsd
  have htr := hNpsd.trace_nonneg
  have hEpos := hE.det_pos
  constructor
  · rw [hdet]; nlinarith
  · intro hD0
    have hN0 : N ≠ 0 := by
      intro h0; apply hD0
      have h3 : E + D = E := by rw [hED, h0, add_zero, mul_one, hB]
      simpa using h3
    have := trace_pos_of_ne_zero hNpsd hN0
    rw [hdet]; nlinarith

/-- A positive definite matrix has a positive Loewner lower bound `ε • 1`. -/
lemma exists_lower_bound {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) :
    ∃ ε : ℝ, 0 < ε ∧ (M - ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  classical
  have hH := hM.isHermitian
  obtain ⟨ε, hε, hle⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ hH.eigenvalues i := by
    rcases isEmpty_or_nonempty (Fin n) with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_min hH.eigenvalues
      exact ⟨hH.eigenvalues i0, hM.eigenvalues_pos i0, hi0⟩
  refine ⟨ε, hε, ?_⟩
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hspec : M = U * diagonal hH.eigenvalues * star U := by
    simpa [Function.id_comp] using hH.spectral_theorem
  have hd : diagonal (fun i => hH.eigenvalues i - ε) = diagonal hH.eigenvalues - ε • 1 := by
    ext i j
    by_cases h : i = j <;> simp [h]
  have h1 : M - ε • 1 = U * diagonal (fun i => hH.eigenvalues i - ε) * Uᴴ := by
    rw [hd, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, ← star_eq_conjTranspose,
      hU, ← hspec]
  rw [h1]
  exact (PosSemidef.diagonal (fun i => sub_nonneg.mpr (hle i))).mul_mul_conjTranspose_same U

/-! ## The functional `J` -/

/-- Matrices with no coefficient crossing the bipartition `S | Sᶜ`. -/
def Bpi (S : Finset (Fin n)) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {B | ∀ i j, ¬ (i ∈ S ↔ j ∈ S) → B i j = 0}

lemma zero_mem_Bpi (S : Finset (Fin n)) : (0 : Matrix (Fin n) (Fin n) ℝ) ∈ Bpi S :=
  fun _ _ _ => rfl

lemma smul_mem_Bpi {S : Finset (Fin n)} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B ∈ Bpi S) (c : ℝ) :
    c • B ∈ Bpi S := fun i j h => by simp [hB i j h]

lemma isClosed_Bpi (S : Finset (Fin n)) : IsClosed (Bpi S) := by
  have : Bpi S = ⋂ i, ⋂ j, {B : Matrix (Fin n) (Fin n) ℝ | ¬ (i ∈ S ↔ j ∈ S) → B i j = 0} := by
    ext B; simp [Bpi]
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases h : (i ∈ S ↔ j ∈ S)
  · simp [h]
  · simp only [h, not_false_eq_true, forall_const]
    exact isClosed_eq (continuous_id.matrix_elem i j) continuous_const

/-- Twice the paper's `f(B)`: `log det (E + (A-B) P (A-B)ᵀ) - log det E`. -/
noncomputable def fval (E P A B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.log (det (E + (A - B) * P * (A - B)ᵀ)) - Real.log (det E)

/-- `J_π(A,E) = inf_{B ∈ 𝔅_π} f(B)/2`. -/
noncomputable def JS (E P A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  sInf ((fun B => fval E P A B / 2) '' Bpi S)

/-- Bipartitions of the units. -/
abbrev Bip (n : ℕ) := {S : Finset (Fin n) // S.Nonempty ∧ Sᶜ.Nonempty}

/-- `J(A,E) = min_π J_π(A,E)` (the covariance `P` is an argument). -/
noncomputable def J (E P A : Matrix (Fin n) (Fin n) ℝ) : ℝ := ⨅ S : Bip n, JS E P A S.1

lemma bip_nonempty (hn : 2 ≤ n) : Nonempty (Bip n) :=
  ⟨⟨{⟨0, by omega⟩}, Finset.singleton_nonempty _, ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩⟩

lemma fval_nonneg {E P : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hP : P.PosSemidef)
    (A B : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ fval E P A B := by
  unfold fval
  have h := (det_add_psd hE (psd_congr hP (A - B))).1
  have := Real.log_le_log hE.det_pos h
  linarith

lemma JS_bdd {E P : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hP : P.PosSemidef)
    (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    BddBelow ((fun B => fval E P A B / 2) '' Bpi S) :=
  ⟨0, by rintro _ ⟨B, -, rfl⟩; exact div_nonneg (fval_nonneg hE hP A B) zero_le_two⟩

lemma JS_le {E P : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hP : P.PosSemidef)
    {A : Matrix (Fin n) (Fin n) ℝ} {S : Finset (Fin n)} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B ∈ Bpi S) : JS E P A S ≤ fval E P A B / 2 :=
  csInf_le (JS_bdd hE hP A S) ⟨B, hB, rfl⟩

lemma le_JS {E P A : Matrix (Fin n) (Fin n) ℝ} {S : Finset (Fin n)} {c : ℝ}
    (h : ∀ B ∈ Bpi S, c ≤ fval E P A B / 2) : c ≤ JS E P A S :=
  le_csInf ⟨_, 0, zero_mem_Bpi S, rfl⟩ (by rintro _ ⟨B, hB, rfl⟩; exact h B hB)

lemma JS_nonneg {E P : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hP : P.PosSemidef)
    (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : 0 ≤ JS E P A S :=
  le_JS (fun B _ => div_nonneg (fval_nonneg hE hP A B) zero_le_two)

lemma continuous_fval {E P : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hP : P.PosSemidef)
    (A : Matrix (Fin n) (Fin n) ℝ) : Continuous fun B => fval E P A B := by
  unfold fval
  refine Continuous.sub (Continuous.log ?_ ?_) continuous_const
  · exact (continuous_const.add (((continuous_const.sub continuous_id).matrix_mul
      continuous_const).matrix_mul (continuous_const.sub continuous_id).matrix_transpose)).matrix_det
  · intro B; exact (hE.add_posSemidef (psd_congr hP (A - B))).det_pos.ne'

/-- Coercivity: `log det (E + C P Cᵀ) ≥ c₀ + log (1 + c₁ C_ij²)` for every entry. -/
lemma log_det_lower {E P : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hP : P.PosDef) :
    ∃ c0 : ℝ, ∃ c1 : ℝ, 0 < c1 ∧ ∀ (C : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n),
      c0 + Real.log (1 + c1 * (C i j) ^ 2) ≤ Real.log (det (E + C * P * Cᵀ)) := by
  obtain ⟨ε, hε, hEε⟩ := exists_lower_bound hE
  obtain ⟨p, hp, hPp⟩ := exists_lower_bound hP
  refine ⟨n * Real.log ε, p / ε, div_pos hp hε, fun C i j => ?_⟩
  have hCC : (C * Cᵀ).PosSemidef := by
    simpa [ct] using posSemidef_self_mul_conjTranspose C
  have hX : (ε • (1 : Matrix (Fin n) (Fin n) ℝ) + p • (C * Cᵀ)).PosDef :=
    (PosDef.one.smul hε).add_posSemidef (hCC.smul hp.le)
  have hdiff : ((E + C * P * Cᵀ) - (ε • 1 + p • (C * Cᵀ))).PosSemidef := by
    have : (E + C * P * Cᵀ) - (ε • 1 + p • (C * Cᵀ)) = (E - ε • 1) + C * (P - p • 1) * Cᵀ := by
      simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]; abel
    rw [this]; exact hEε.add (psd_congr hPp C)
  have hle1 : det (ε • 1 + p • (C * Cᵀ)) ≤ det (E + C * P * Cᵀ) := by
    have := (det_add_psd hX hdiff).1
    simpa using this
  have hX' : ε • (1 : Matrix (Fin n) (Fin n) ℝ) + p • (C * Cᵀ) = ε • (1 + (p / ε) • (C * Cᵀ)) := by
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hε.ne']
  have hNpsd : ((p / ε) • (C * Cᵀ)).PosSemidef := hCC.smul (div_pos hp hε).le
  have hdetX : det (ε • (1 : Matrix (Fin n) (Fin n) ℝ) + p • (C * Cᵀ)) =
      ε ^ n * det (1 + (p / ε) • (C * Cᵀ)) := by
    rw [hX', det_smul, Fintype.card_fin]
  have htr : (p / ε) * (C i j) ^ 2 ≤ ((p / ε) • (C * Cᵀ)).trace := by
    rw [trace_smul, smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (div_pos hp hε).le
    have : (C * Cᵀ).trace = ∑ k, ∑ l, C k l ^ 2 := by simp [trace, mul_apply, sq]
    rw [this]
    calc C i j ^ 2 ≤ ∑ l, C i l ^ 2 :=
          Finset.single_le_sum (f := fun l => C i l ^ 2) (fun l _ => sq_nonneg (C i l))
            (Finset.mem_univ j)
      _ ≤ ∑ k, ∑ l, C k l ^ 2 :=
          Finset.single_le_sum (f := fun k => ∑ l, C k l ^ 2)
            (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (C k l))) (Finset.mem_univ i)
  have hdet1 := one_add_trace_le_det hNpsd
  have hpos1 : 0 < 1 + p / ε * C i j ^ 2 := by positivity
  have hεn : 0 < ε ^ n := pow_pos hε n
  calc (n : ℝ) * Real.log ε + Real.log (1 + p / ε * C i j ^ 2)
      = Real.log (ε ^ n * (1 + p / ε * C i j ^ 2)) := by
        rw [Real.log_mul hεn.ne' hpos1.ne', Real.log_pow]
    _ ≤ Real.log (det (E + C * P * Cᵀ)) := by
        apply Real.log_le_log (by positivity)
        calc ε ^ n * (1 + p / ε * C i j ^ 2) ≤ ε ^ n * det (1 + (p / ε) • (C * Cᵀ)) := by
              apply mul_le_mul_of_nonneg_left _ hεn.le; linarith
          _ = det (ε • 1 + p • (C * Cᵀ)) := hdetX.symm
          _ ≤ _ := hle1

/-- Existence of a minimizer of `f` on `𝔅_π` (continuity and coercivity). -/
theorem exists_minimizer {E P : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hP : P.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    ∃ B ∈ Bpi S, ∀ B' ∈ Bpi S, fval E P A B ≤ fval E P A B' := by
  obtain ⟨c0, c1, hc1, hlow⟩ := log_det_lower hE hP
  set V0 := fval E P A 0 with hV0
  set W := V0 + Real.log (det E) - c0 with hW
  set K := Real.exp W / c1 with hK
  set R := 1 + K with hR
  let box : Set (Matrix (Fin n) (Fin n) ℝ) :=
    Set.univ.pi fun i => Set.univ.pi fun j => Set.Icc (A i j - R) (A i j + R)
  have hbox : IsCompact box := isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc
  let Ks := Bpi S ∩ {B | fval E P A B ≤ V0}
  have hcont := continuous_fval hE hP.posSemidef A
  have hKclosed : IsClosed Ks := (isClosed_Bpi S).inter (isClosed_le hcont continuous_const)
  have hKsub : Ks ⊆ box := by
    rintro B ⟨_, hBV⟩
    show B ∈ box
    intro i _ j _
    have h1 := hlow (A - B) i j
    have h2 : Real.log (det (E + (A - B) * P * (A - B)ᵀ)) ≤ V0 + Real.log (det E) := by
      simp only [Set.mem_setOf_eq, fval] at hBV; linarith
    have h3 : Real.log (1 + c1 * ((A - B) i j) ^ 2) ≤ W := by rw [hW]; linarith
    have hpos : 0 < 1 + c1 * ((A - B) i j) ^ 2 := by positivity
    have h4 : 1 + c1 * ((A - B) i j) ^ 2 ≤ Real.exp W := by
      rwa [Real.log_le_iff_le_exp hpos] at h3
    have h5 : ((A - B) i j) ^ 2 ≤ K := by
      rw [hK, le_div_iff₀ hc1]; nlinarith
    have hK0 : 0 ≤ K := by positivity
    have h6 : |(A - B) i j| ≤ R := by
      by_cases h : |(A - B) i j| ≤ 1
      · rw [hR]; linarith
      · push_neg at h
        have : |(A - B) i j| ≤ ((A - B) i j) ^ 2 := by
          rw [← sq_abs]; nlinarith [abs_nonneg ((A - B) i j)]
        rw [hR]; linarith
    rw [sub_apply, abs_le] at h6
    exact ⟨by linarith [h6.1], by linarith [h6.2]⟩
  have hKc : IsCompact Ks := hbox.of_isClosed_subset hKclosed hKsub
  have h0K : (0 : Matrix (Fin n) (Fin n) ℝ) ∈ Ks := ⟨zero_mem_Bpi S, show fval E P A 0 ≤ V0 from le_refl _⟩
  obtain ⟨Bs, hBsK, hmin⟩ := hKc.exists_isMinOn ⟨0, h0K⟩ hcont.continuousOn
  rw [isMinOn_iff] at hmin
  refine ⟨Bs, hBsK.1, fun B' hB' => ?_⟩
  by_cases hB'V : fval E P A B' ≤ V0
  · exact hmin B' ⟨hB', hB'V⟩
  · push_neg at hB'V
    have := hmin 0 h0K
    linarith


/-! ## The stationary covariance of `tA` as a series -/

/-- `P_t = ∑_j t^{2j} A^j E (A^j)ᵀ`, the stationary covariance of `tA` with noise `E`. -/
noncomputable def Pt (A E : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑' j : ℕ, (t ^ (2 * j)) • (A ^ j * E * (A ^ j)ᵀ)

/-- The series defining `P_t` converges. -/
def SummableAt (A E : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Prop :=
  Summable fun j : ℕ => (t ^ (2 * j)) • (A ^ j * E * (A ^ j)ᵀ)

lemma psd_tsum {f : ℕ → Matrix (Fin n) (Fin n) ℝ} (hf : Summable f)
    (h : ∀ j, (f j).PosSemidef) : (∑' j, f j).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · show (∑' j, f j)ᴴ = ∑' j, f j
    rw [Matrix.conjTranspose_tsum]
    exact tsum_congr (fun j => (h j).1)
  · let g : Matrix (Fin n) (Fin n) ℝ →+ ℝ :=
      { toFun := fun M => star x ⬝ᵥ (M *ᵥ x)
        map_zero' := by simp
        map_add' := fun M N => by simp [add_mulVec, dotProduct_add] }
    have hg : Continuous g := by
      show Continuous fun M : Matrix (Fin n) (Fin n) ℝ => star x ⬝ᵥ (M *ᵥ x)
      exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    have := (hf.hasSum.map g hg).tsum_eq
    show 0 ≤ g (∑' j, f j)
    rw [← this]
    exact tsum_nonneg (fun j => (h j).2 x)

lemma term_psd {E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (A : Matrix (Fin n) (Fin n) ℝ)
    (j : ℕ) : (A ^ j * E * (A ^ j)ᵀ).PosSemidef :=
  psd_congr hE.posSemidef (A ^ j)

lemma pow_two_mul_nonneg (t : ℝ) (j : ℕ) : 0 ≤ t ^ (2 * j) := by
  rw [pow_mul]; exact pow_nonneg (sq_nonneg t) j

lemma Pt_psd {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) {t : ℝ} (h : SummableAt A E t) :
    (Pt A E t).PosSemidef :=
  psd_tsum h (fun j => (term_psd hE A j).smul (pow_two_mul_nonneg t j))

/-- Summability at `t₂` gives summability at every `t₁ ∈ [0, t₂]`. -/
lemma summableAt_mono {A E : Matrix (Fin n) (Fin n) ℝ} {t1 t2 : ℝ} (h1 : 0 ≤ t1)
    (h12 : t1 ≤ t2) (h : SummableAt A E t2) : SummableAt A E t1 := by
  unfold SummableAt at *
  refine Pi.summable.mpr fun a => Pi.summable.mpr fun b => ?_
  have hab : Summable fun j : ℕ => ((t2 ^ (2 * j)) • (A ^ j * E * (A ^ j)ᵀ)) a b :=
    Pi.summable.mp (Pi.summable.mp h a) b
  refine Summable.of_norm_bounded hab.abs (fun j => ?_)
  simp only [smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  rw [abs_of_nonneg (pow_nonneg h1 _), abs_of_nonneg (pow_nonneg (h1.trans h12) _)]
  exact pow_le_pow_left₀ h1 h12 _

lemma summableAt_zero (A E : Matrix (Fin n) (Fin n) ℝ) : SummableAt A E 0 := by
  unfold SummableAt
  apply summable_of_ne_finset_zero (s := {0})
  intro j hj
  have : j ≠ 0 := by simpa using hj
  simp [zero_pow (show 2 * j ≠ 0 by omega)]

lemma Pt_zero (A E : Matrix (Fin n) (Fin n) ℝ) : Pt A E 0 = E := by
  unfold Pt
  rw [tsum_eq_single 0 (fun j hj => by simp [zero_pow (show 2 * j ≠ 0 by omega)])]
  simp

/-- Step (1) of the proof: `P_t` is nondecreasing in the Loewner order. -/
theorem Pt_mono {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) {t1 t2 : ℝ} (h1 : 0 ≤ t1)
    (h12 : t1 ≤ t2) (hs2 : SummableAt A E t2) : (Pt A E t2 - Pt A E t1).PosSemidef := by
  have hs1 := summableAt_mono h1 h12 hs2
  unfold Pt
  rw [← hs2.tsum_sub hs1]
  refine psd_tsum (hs2.sub hs1) (fun j => ?_)
  rw [← sub_smul]
  exact (term_psd hE A j).smul (sub_nonneg.mpr (pow_le_pow_left₀ h1 h12 _))

lemma Pt_sub_E_psd {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) {t : ℝ} (ht : 0 ≤ t)
    (hs : SummableAt A E t) : (Pt A E t - E).PosSemidef := by
  simpa [Pt_zero] using Pt_mono hE le_rfl ht hs

lemma Pt_posDef {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) {t : ℝ} (ht : 0 ≤ t)
    (hs : SummableAt A E t) : (Pt A E t).PosDef := by
  have := hE.add_posSemidef (Pt_sub_E_psd hE ht hs)
  simpa using this

/-- Step (1), scaled form: `t ↦ t² P_t` is nondecreasing in the Loewner order. -/
theorem sq_smul_Pt_mono {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) {t1 t2 : ℝ}
    (h1 : 0 ≤ t1) (h12 : t1 ≤ t2) (hs2 : SummableAt A E t2) :
    (t2 ^ 2 • Pt A E t2 - t1 ^ 2 • Pt A E t1).PosSemidef := by
  have hs1 := summableAt_mono h1 h12 hs2
  have h : t2 ^ 2 • Pt A E t2 - t1 ^ 2 • Pt A E t1 =
      t2 ^ 2 • (Pt A E t2 - Pt A E t1) + (t2 ^ 2 - t1 ^ 2) • Pt A E t1 := by
    rw [smul_sub, sub_smul]; abel
  rw [h]
  exact ((Pt_mono hE h1 h12 hs2).smul (sq_nonneg t2)).add
    ((Pt_psd hE hs1).smul (sub_nonneg.mpr (pow_le_pow_left₀ h1 h12 2)))

/-- The residual `R_t(B') = E + t² (A - B') P_t (A - B')ᵀ`. -/
noncomputable def Rt (A E B' : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  E + t ^ 2 • ((A - B') * Pt A E t * (A - B')ᵀ)

/-- Equation `eq:resid-incr`: `R_{t₂}(B') - R_{t₁}(B') ⪰ 0` for `0 ≤ t₁ ≤ t₂`. -/
theorem resid_incr {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) {t1 t2 : ℝ}
    (h1 : 0 ≤ t1) (h12 : t1 ≤ t2) (hs2 : SummableAt A E t2) (B' : Matrix (Fin n) (Fin n) ℝ) :
    (Rt A E B' t2 - Rt A E B' t1).PosSemidef ∧
    Rt A E B' t2 - Rt A E B' t1 =
      t2 ^ 2 • ((A - B') * (Pt A E t2 - Pt A E t1) * (A - B')ᵀ) +
      (t2 ^ 2 - t1 ^ 2) • ((A - B') * Pt A E t1 * (A - B')ᵀ) := by
  have hs1 := summableAt_mono h1 h12 hs2
  have heq : Rt A E B' t2 - Rt A E B' t1 =
      t2 ^ 2 • ((A - B') * (Pt A E t2 - Pt A E t1) * (A - B')ᵀ) +
      (t2 ^ 2 - t1 ^ 2) • ((A - B') * Pt A E t1 * (A - B')ᵀ) := by
    unfold Rt
    simp only [mul_sub, sub_mul, smul_sub, sub_smul]
    abel
  refine ⟨?_, heq⟩
  rw [heq]
  exact ((psd_congr (Pt_mono hE h1 h12 hs2) _).smul (sq_nonneg t2)).add
    ((psd_congr (Pt_psd hE hs1) _).smul (sub_nonneg.mpr (pow_le_pow_left₀ h1 h12 2)))


/-! ## Part (a): monotonicity of `t ↦ J(tA, E)` -/

/-- `J(tA, E)`, with the stationary covariance `P_t` of `tA`. -/
noncomputable def Jt (A E : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ := J E (Pt A E t) (t • A)

/-- The domain of the scaling parameter: `t ≥ 0` with a convergent covariance series.
It contains `[0, 1/spr(A))`, and it is an interval containing `0` (`summableAt_mono`). -/
def Dom (A E : Matrix (Fin n) (Fin n) ℝ) : Set ℝ := {t | 0 ≤ t ∧ SummableAt A E t}

/-- Core comparison (step (2) of the proof, in the original variable `B = t₂ B'`):
`f_{t₁}((t₁/t₂) B) ≤ f_{t₂}(B)`, and strictly if `t₁ < t₂` and `t₂A - B` has a nonzero entry. -/
theorem fval_scaled {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) {t1 t2 : ℝ}
    (h1 : 0 ≤ t1) (h12 : t1 ≤ t2) (hs2 : SummableAt A E t2) (B : Matrix (Fin n) (Fin n) ℝ) :
    fval E (Pt A E t1) (t1 • A) ((t1 / t2) • B) ≤ fval E (Pt A E t2) (t2 • A) B ∧
    (t1 < t2 → ∀ a b, (t2 • A - B) a b ≠ 0 →
      fval E (Pt A E t1) (t1 • A) ((t1 / t2) • B) < fval E (Pt A E t2) (t2 • A) B) := by
  have hs1 := summableAt_mono h1 h12 hs2
  have ht2 : 0 ≤ t2 := h1.trans h12
  set P1 := Pt A E t1 with hP1
  set P2 := Pt A E t2 with hP2
  set c := t1 / t2 with hc
  have hc0 : 0 ≤ c := div_nonneg h1 ht2
  have hc1 : c ≤ 1 := div_le_one_of_le₀ h12 ht2
  have hct : c * t2 = t1 := by
    rcases eq_or_lt_of_le ht2 with h | h
    · have : t1 = 0 := le_antisymm (h ▸ h12) h1
      rw [hc, ← h, this]; simp
    · exact div_mul_cancel₀ t1 h.ne'
  have hC : t1 • A - c • B = c • (t2 • A - B) := by rw [smul_sub, smul_smul, hct]
  set C0 := t2 • A - B with hC0
  have hP1psd : P1.PosSemidef := Pt_psd hE hs1
  -- the two residuals
  set R1 := E + (c • C0) * P1 * (c • C0)ᵀ with hR1
  set R2 := E + C0 * P2 * C0ᵀ with hR2
  have hR1pd : R1.PosDef := hE.add_posSemidef (psd_congr hP1psd _)
  have hQ : P2 - c ^ 2 • P1 = (P2 - P1) + (1 - c ^ 2) • P1 := by
    rw [sub_smul, one_smul]; abel
  have hQpsd : (P2 - c ^ 2 • P1).PosSemidef := by
    rw [hQ]
    exact (Pt_mono hE h1 h12 hs2).add (hP1psd.smul (by nlinarith))
  have hsum : R1 + C0 * (P2 - c ^ 2 • P1) * C0ᵀ = R2 := by
    rw [hR1, hR2]
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_sub, sub_mul, sq]
    abel
  have hD := psd_congr hQpsd C0
  have key := det_add_psd hR1pd hD
  rw [hsum] at key
  have hfv1 : fval E P1 (t1 • A) (c • B) = Real.log (det R1) - Real.log (det E) := by
    rw [fval, hC]
  have hfv2 : fval E P2 (t2 • A) B = Real.log (det R2) - Real.log (det E) := by
    rw [fval]
  refine ⟨?_, ?_⟩
  · rw [hfv1, hfv2]
    have := Real.log_le_log hR1pd.det_pos key.1
    linarith
  · intro hlt a b hab
    have ht2pos : 0 < t2 := h1.trans_lt hlt
    have hc1' : c < 1 := (div_lt_one ht2pos).mpr hlt
    -- the increment dominates `(1 - c²) C₀ E C₀ᵀ`, whose `(a,a)` entry is positive
    have hdom : (C0 * (P2 - c ^ 2 • P1) * C0ᵀ - (1 - c ^ 2) • (C0 * E * C0ᵀ)).PosSemidef := by
      have h3 : C0 * (P2 - c ^ 2 • P1) * C0ᵀ - (1 - c ^ 2) • (C0 * E * C0ᵀ) =
          C0 * ((P2 - P1) + (1 - c ^ 2) • (P1 - E)) * C0ᵀ := by
        rw [hQ]; simp only [mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          smul_sub]; abel
      rw [h3]
      exact psd_congr ((Pt_mono hE h1 h12 hs2).add
        ((Pt_sub_E_psd hE h1 hs1).smul (by nlinarith))) C0
    have hrow : (fun k => C0 a k) ≠ 0 := fun h => hab (congrFun h b)
    have hdiag : 0 < (C0 * E * C0ᵀ) a a := by
      have := hE.2 (fun k => C0 a k) hrow
      convert this using 1
      simp only [mul_apply, transpose_apply, dotProduct, mulVec, star_trivial, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    have hdiag2 : 0 ≤ (C0 * (P2 - c ^ 2 • P1) * C0ᵀ - (1 - c ^ 2) • (C0 * E * C0ᵀ)) a a := by
      have := hdom.2 (Pi.single a 1)
      simpa [dotProduct, mulVec, Pi.single_apply] using this
    have hne : C0 * (P2 - c ^ 2 • P1) * C0ᵀ ≠ 0 := by
      intro h0
      rw [h0, zero_sub, neg_apply, smul_apply, smul_eq_mul] at hdiag2
      have : 0 < (1 - c ^ 2) * (C0 * E * C0ᵀ) a a := mul_pos (by nlinarith) hdiag
      linarith
    rw [hfv1, hfv2]
    have := Real.log_lt_log hR1pd.det_pos (key.2 hne)
    linarith

/-- Part (a), monotonicity: `t ↦ J(tA, E)` is nondecreasing on its domain. -/
theorem Jt_mono {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) {t1 t2 : ℝ} (h1 : 0 ≤ t1)
    (h12 : t1 ≤ t2) (hs2 : SummableAt A E t2) : Jt A E t1 ≤ Jt A E t2 := by
  have hs1 := summableAt_mono h1 h12 hs2
  unfold Jt J
  apply ciInf_mono (Set.finite_range _).bddBelow
  intro S
  apply le_JS
  intro B hB
  calc JS E (Pt A E t1) (t1 • A) S.1 ≤ fval E (Pt A E t1) (t1 • A) ((t1 / t2) • B) / 2 :=
        JS_le hE (Pt_psd hE hs1) (smul_mem_Bpi hB _)
    _ ≤ fval E (Pt A E t2) (t2 • A) B / 2 := by
        have := (fval_scaled hE h1 h12 hs2 B).1
        linarith

/-- Part (a), value at `0`: `J(0, E) = 0`. -/
theorem Jt_zero {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) : Jt A E 0 = 0 := by
  unfold Jt J
  rw [Pt_zero, zero_smul]
  have h : ∀ S : Bip n, JS E E 0 S.1 = 0 := by
    intro S
    apply IsLeast.csInf_eq
    refine ⟨⟨0, zero_mem_Bpi _, ?_⟩, ?_⟩
    · simp [fval]
    · rintro _ ⟨B, -, rfl⟩
      exact div_nonneg (fval_nonneg hE hE.posSemidef 0 B) zero_le_two
  simp only [h]
  exact Real.iInf_const_zero


/-! ## Part (a): strict monotonicity for connected support -/

/-- The undirected graph of the off-diagonal support of `A`. -/
def supportGraph (A : Matrix (Fin n) (Fin n) ℝ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => A i j ≠ 0

/-- If the support of `A` is connected, `A ∉ 𝔅_π` for every bipartition `π`. -/
lemma not_mem_Bpi_of_connected {A : Matrix (Fin n) (Fin n) ℝ} (hA : (supportGraph A).Connected)
    {S : Finset (Fin n)} (hS : S.Nonempty ∧ Sᶜ.Nonempty) : A ∉ Bpi S := by
  intro hB
  obtain ⟨i, hi⟩ := hS.1
  obtain ⟨j, hj⟩ := hS.2
  have hreach := hA.preconnected i j
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have key : ∀ k, Relation.ReflTransGen (supportGraph A).Adj i k → k ∈ S := by
    intro k hk
    induction hk with
    | refl => exact hi
    | tail _ hadj ih =>
      rename_i b c
      by_contra hc
      simp only [supportGraph, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨_, h1 | h1⟩ := hadj
      · exact h1 (hB _ _ (by tauto))
      · exact h1 (hB _ _ (by tauto))
  exact (Finset.mem_compl.mp hj) (key j hreach)

/-- Part (a), strictness: if the undirected support of `A` is connected and `n ≥ 2`, then
`t ↦ J(tA, E)` is strictly increasing. -/
theorem Jt_strictMono {A E : Matrix (Fin n) (Fin n) ℝ} (hn : 2 ≤ n) (hE : E.PosDef)
    (hA : (supportGraph A).Connected) {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h12 : t1 < t2)
    (hs2 : SummableAt A E t2) : Jt A E t1 < Jt A E t2 := by
  have hs1 := summableAt_mono h1 h12.le hs2
  have ht2 : 0 < t2 := h1.trans_lt h12
  haveI : Nonempty (Bip n) := bip_nonempty hn
  obtain ⟨S0, hS0⟩ :=
    exists_eq_ciInf_of_finite (f := fun S : Bip n => JS E (Pt A E t2) (t2 • A) S.1)
  unfold Jt J
  rw [← hS0]
  refine lt_of_le_of_lt (ciInf_le (Set.finite_range _).bddBelow S0) ?_
  have hP2 : (Pt A E t2).PosDef := Pt_posDef hE ht2.le hs2
  obtain ⟨Bs, hBs, hmin⟩ := exists_minimizer hE hP2 (t2 • A) S0.1
  have hJS2 : JS E (Pt A E t2) (t2 • A) S0.1 = fval E (Pt A E t2) (t2 • A) Bs / 2 := by
    apply IsLeast.csInf_eq
    refine ⟨⟨Bs, hBs, rfl⟩, ?_⟩
    rintro _ ⟨B, hB, rfl⟩
    have := hmin B hB
    show fval E (Pt A E t2) (t2 • A) Bs / 2 ≤ fval E (Pt A E t2) (t2 • A) B / 2
    linarith
  rw [hJS2]
  obtain ⟨a, b, hab_cross, hAab⟩ : ∃ a b, ¬ (a ∈ S0.1 ↔ b ∈ S0.1) ∧ A a b ≠ 0 := by
    have := not_mem_Bpi_of_connected hA S0.2
    simp only [Bpi, Set.mem_setOf_eq, not_forall] at this
    obtain ⟨a, b, h, h'⟩ := this
    exact ⟨a, b, h, h'⟩
  have hC : (t2 • A - Bs) a b ≠ 0 := by
    rw [sub_apply, smul_apply, hBs a b hab_cross, sub_zero, smul_eq_mul]
    exact mul_ne_zero ht2.ne' hAab
  calc JS E (Pt A E t1) (t1 • A) S0.1 ≤ fval E (Pt A E t1) (t1 • A) ((t1 / t2) • Bs) / 2 :=
        JS_le hE (Pt_psd hE hs1) (smul_mem_Bpi hBs _)
    _ < fval E (Pt A E t2) (t2 • A) Bs / 2 := by
        have := (fval_scaled hE h1 h12.le hs2 Bs).2 h12 a b hC
        linarith

/-! ## Proposition `prop:scaling`, part (a), packaged -/

/-- **Proposition (scaling), part (a), monotonicity.** For `E ≻ 0`, `t ↦ J(tA, E)` is
nondecreasing on `Dom A E = {t ≥ 0 | the covariance series of tA converges}`. -/
theorem prop_scaling_a_monotone {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) :
    MonotoneOn (Jt A E) (Dom A E) :=
  fun _ ht1 _ ht2 h12 => Jt_mono hE ht1.1 h12 ht2.2

/-- **Proposition (scaling), part (a), value at `0`.** `J(0·A, E) = 0`. -/
theorem prop_scaling_a_zero {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) : Jt A E 0 = 0 :=
  Jt_zero hE

/-- **Proposition (scaling), part (a), strictness.** For `n ≥ 2`, `E ≻ 0` and a matrix `A` whose
undirected off-diagonal support is connected, `t ↦ J(tA, E)` is strictly increasing on
`Dom A E`. -/
theorem prop_scaling_a_strictMono {A E : Matrix (Fin n) (Fin n) ℝ} (hn : 2 ≤ n)
    (hE : E.PosDef) (hA : (supportGraph A).Connected) : StrictMonoOn (Jt A E) (Dom A E) :=
  fun _ ht1 _ ht2 h12 => Jt_strictMono hn hE hA ht1.1 h12 ht2.2

/-- `Dom A E` is an interval containing `0`. -/
theorem dom_ordConnected (A E : Matrix (Fin n) (Fin n) ℝ) :
    0 ∈ Dom A E ∧ ∀ t1 t2, 0 ≤ t1 → t1 ≤ t2 → t2 ∈ Dom A E → t1 ∈ Dom A E :=
  ⟨⟨le_rfl, summableAt_zero A E⟩, fun _ _ h1 h12 h2 => ⟨h1, summableAt_mono h1 h12 h2.2⟩⟩


/-- Non-vacuity of part (a): for `n = 2`, `E = 1` and the nilpotent `A = !![0, 1; 0, 0]`, whose
support is connected, every `t ≥ 0` lies in the domain, so `t ↦ J(tA, 1)` is strictly increasing
on `[0, ∞)`. -/
example : StrictMonoOn (Jt !![(0 : ℝ), 1; 0, 0] 1) (Set.Ici 0) := by
  set A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0] with hAdef
  have hA2 : A ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hsum : ∀ t, SummableAt A 1 t := by
    intro t
    apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro j hj
    have : 2 ≤ j := by simpa using hj
    simp [pow_eq_zero_of_le this hA2]
  have hconn : (supportGraph A).Connected := by
    have hadj : (supportGraph A).Adj 0 1 := by simp [supportGraph, SimpleGraph.fromRel_adj, A]
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ⟨0⟩⟩
    fin_cases u <;> fin_cases v
    exacts [SimpleGraph.Reachable.refl _, hadj.reachable, hadj.symm.reachable,
      SimpleGraph.Reachable.refl _]
  have h := prop_scaling_a_strictMono (by norm_num) PosDef.one hconn
  intro t1 ht1 t2 ht2 h12
  exact h ⟨ht1, hsum t1⟩ ⟨ht2, hsum t2⟩ h12




/-! ## Stationary covariance series and the Lyapunov equation -/

/-- The series `∑_j M^j E (M^j)ᵀ`, the stationary covariance of `x ↦ M x + noise(E)`. -/
noncomputable def Pser (M E : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑' j : ℕ, M ^ j * E * (M ^ j)ᵀ

/-- Convergence of that series. -/
def SerSummable (M E : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Summable fun j : ℕ => M ^ j * E * (M ^ j)ᵀ

lemma Pser_psd {M E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (h : SerSummable M E) :
    (Pser M E).PosSemidef :=
  psd_tsum h (fun j => psd_congr hE.posSemidef (M ^ j))

/-- The series solves the Lyapunov (Stein) equation `P = M P Mᵀ + E`. -/
theorem Pser_lyap {M E : Matrix (Fin n) (Fin n) ℝ} (h : SerSummable M E) :
    Pser M E = M * Pser M E * Mᵀ + E := by
  have hs : Summable fun j : ℕ => M ^ j * E * (M ^ j)ᵀ := h
  unfold Pser
  conv_lhs => rw [hs.tsum_eq_zero_add]
  have hterm : ∀ j : ℕ, M ^ (j + 1) * E * (M ^ (j + 1))ᵀ = M * (M ^ j * E * (M ^ j)ᵀ) * Mᵀ := by
    intro j; rw [pow_succ', transpose_mul]; simp only [Matrix.mul_assoc]
  simp only [hterm]
  rw [Summable.tsum_mul_right _ (hs.mul_left M), Summable.tsum_mul_left _ hs]
  rw [pow_zero, transpose_one, one_mul, mul_one, add_comm]

lemma Pser_posDef {M E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (h : SerSummable M E) :
    (Pser M E).PosDef := by
  rw [Pser_lyap h, add_comm]
  exact hE.add_posSemidef (psd_congr (Pser_psd hE h) M)

lemma Pt_term (A E : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (j : ℕ) :
    (t • A) ^ j * E * ((t • A) ^ j)ᵀ = (t ^ (2 * j)) • (A ^ j * E * (A ^ j)ᵀ) := by
  simp only [smul_pow, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← pow_add, two_mul]

/-- `P_t` is the stationary covariance of `tA`: `P_t = (tA) P_t (tA)ᵀ + E`. -/
theorem Pt_lyap {A E : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (hs : SummableAt A E t) :
    Pt A E t = (t • A) * Pt A E t * (t • A)ᵀ + E := by
  have h1 : Pt A E t = Pser (t • A) E := by unfold Pt Pser; simp only [Pt_term]
  have h2 : SerSummable (t • A) E := by
    unfold SerSummable; simp only [Pt_term]; exact hs
  rw [h1]; exact Pser_lyap h2

/-! ## Part (b): fixed scalar self-coupling `A(c) = aI + cW` -/

/-- A Loewner upper bound `κ E ⪰ Q` for a symmetric `Q` and `E ≻ 0`. -/
lemma exists_upper_bound {E Q : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hQ : Q.IsHermitian) :
    ∃ κ : ℝ, 0 ≤ κ ∧ (κ • E - Q).PosSemidef := by
  classical
  set μ := ∑ i, |hQ.eigenvalues i| with hμ
  have hle : ∀ i, hQ.eigenvalues i ≤ μ := fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |hQ.eigenvalues j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  set U : Matrix (Fin n) (Fin n) ℝ := (hQ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hQ.eigenvectorUnitary.2
  have hspec : Q = U * diagonal hQ.eigenvalues * star U := by
    simpa [Function.id_comp] using hQ.spectral_theorem
  have hd : diagonal (fun i => μ - hQ.eigenvalues i) = μ • 1 - diagonal hQ.eigenvalues := by
    ext i j
    by_cases h : i = j <;> simp [h]
  have h1 : μ • 1 - Q = U * diagonal (fun i => μ - hQ.eigenvalues i) * Uᴴ := by
    rw [hd, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, ← star_eq_conjTranspose,
      hU, ← hspec]
  have hμQ : (μ • 1 - Q).PosSemidef := by
    rw [h1]
    exact (PosSemidef.diagonal (fun i => sub_nonneg.mpr (hle i))).mul_mul_conjTranspose_same U
  obtain ⟨ε, hε, hEε⟩ := exists_lower_bound hE
  refine ⟨μ / ε, div_nonneg hμ0 hε.le, ?_⟩
  have : (μ / ε) • E - Q = (μ / ε) • (E - ε • 1) + (μ • 1 - Q) := by
    rw [smul_sub, smul_smul, div_mul_cancel₀ _ hε.ne']; abel
  rw [this]
  exact (hEε.smul (div_nonneg hμ0 hε.le)).add hμQ

/-- Stein-equation positivity: if `D = M D Mᵀ + S` with `S ⪰ 0`, `D = Q₂ - Q₁` with `Q_i ⪰ 0`,
and `∑ M^j E (M^j)ᵀ` converges for some `E ≻ 0`, then `D ⪰ 0`. -/
lemma stein_psd {M D S E Q1 Q2 : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) (hS : S.PosSemidef)
    (hD : D = M * D * Mᵀ + S) (hDQ : D = Q2 - Q1) (hQ2 : Q2.PosSemidef) (hQ1 : Q1.PosSemidef)
    (hsum : SerSummable M E) : D.PosSemidef := by
  have hSD : S = D - M * D * Mᵀ := by
    calc S = (M * D * Mᵀ + S) - M * D * Mᵀ := by abel
      _ = D - M * D * Mᵀ := by rw [← hD]
  have iter : ∀ k : ℕ, (D - M ^ k * D * (M ^ k)ᵀ).PosSemidef := by
    intro k
    induction k with
    | zero => simpa using PosSemidef.zero
    | succ k ih =>
      have step : D - M ^ (k + 1) * D * (M ^ (k + 1))ᵀ =
          (D - M ^ k * D * (M ^ k)ᵀ) + M ^ k * S * (M ^ k)ᵀ := by
        rw [hSD, pow_succ, transpose_mul, mul_sub, sub_mul]
        simp only [Matrix.mul_assoc]
        abel
      rw [step]; exact ih.add (psd_congr hS _)
  obtain ⟨κ, hκ, hκQ⟩ := exists_upper_bound hE hQ1.1
  have bound : ∀ k : ℕ, (D + κ • (M ^ k * E * (M ^ k)ᵀ)).PosSemidef := by
    intro k
    have h1 : M ^ k * D * (M ^ k)ᵀ = M ^ k * Q2 * (M ^ k)ᵀ - M ^ k * Q1 * (M ^ k)ᵀ := by
      rw [hDQ, mul_sub, sub_mul]
    have h2 : D + κ • (M ^ k * E * (M ^ k)ᵀ) =
        (D - M ^ k * D * (M ^ k)ᵀ) + M ^ k * (Q2 + (κ • E - Q1)) * (M ^ k)ᵀ := by
      rw [h1, mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul]; abel
    rw [h2]
    exact (iter k).add (psd_congr (hQ2.add hκQ) _)
  refine ⟨hDQ ▸ hQ2.1.sub hQ1.1, fun x => ?_⟩
  let g : Matrix (Fin n) (Fin n) ℝ → ℝ := fun N => star x ⬝ᵥ (N *ᵥ x)
  have hg : Continuous g :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  have hT : Filter.Tendsto (fun k : ℕ => M ^ k * E * (M ^ k)ᵀ) Filter.atTop (nhds 0) :=
    Summable.tendsto_atTop_zero hsum
  have hgT : Filter.Tendsto (fun k : ℕ => -κ * g (M ^ k * E * (M ^ k)ᵀ)) Filter.atTop (nhds 0) := by
    have := ((hg.tendsto 0).comp hT).const_mul (-κ)
    simpa [g] using this
  refine le_of_tendsto' hgT (fun k => ?_)
  have := (bound k).2 x
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul] at this
  show -κ * g (M ^ k * E * (M ^ k)ᵀ) ≤ star x ⬝ᵥ (D *ᵥ x)
  simp only [g]
  linarith

/-- `A(c) = a I + c W`. -/
def Acoup (a c : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := a • 1 + c • W

lemma Ab_expand (a c : ℝ) (W P : Matrix (Fin n) (Fin n) ℝ) :
    Acoup a c W * P * (Acoup a c W)ᵀ =
      a ^ 2 • P + (a * c) • (W * P + P * Wᵀ) + c ^ 2 • (W * P * Wᵀ) := by
  unfold Acoup
  simp only [transpose_add, transpose_smul, transpose_one, add_mul, mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  module

/-- Step of part (b): `Q(c) = c² P(c)` satisfies `Q(c₂) - Q(c₁) ⪰ (c₂ - c₁)² E`
(the finite-difference form of `eq:S-identity`). -/
theorem Qb_mono {a : ℝ} (ha : |a| ≤ 1) {W E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    {c1 c2 : ℝ} (h1 : 0 ≤ c1) (h12 : c1 ≤ c2)
    (hs1 : SerSummable (Acoup a c1 W) E) (hs2 : SerSummable (Acoup a c2 W) E) :
    (c2 ^ 2 • Pser (Acoup a c2 W) E - c1 ^ 2 • Pser (Acoup a c1 W) E - (c2 - c1) ^ 2 • E).PosSemidef := by
  have L1 := Pser_lyap hs1
  have L2 := Pser_lyap hs2
  have hP1 := Pser_psd hE hs1
  have hP2 := Pser_psd hE hs2
  generalize hA1 : Acoup a c1 W = A1 at L1 hP1 hs1
  generalize hA2 : Acoup a c2 W = A2 at L2 hP2 hs2
  generalize hQ1 : Pser A1 E = P1 at L1 hP1
  generalize hQ2 : Pser A2 E = P2 at L2 hP2
  have x1 : A1 * P1 * A1ᵀ = a ^ 2 • P1 + (a * c1) • (W * P1 + P1 * Wᵀ) + c1 ^ 2 • (W * P1 * Wᵀ) := by
    rw [← hA1]; exact Ab_expand a c1 W P1
  have x2 : A2 * P1 * A2ᵀ = a ^ 2 • P1 + (a * c2) • (W * P1 + P1 * Wᵀ) + c2 ^ 2 • (W * P1 * Wᵀ) := by
    rw [← hA2]; exact Ab_expand a c2 W P1
  set D := c2 ^ 2 • P2 - c1 ^ 2 • P1 with hD
  set St := A2 * (c1 ^ 2 • P1) * A2ᵀ - A1 * (c1 ^ 2 • P1) * A1ᵀ + (c2 ^ 2 - c1 ^ 2) • E with hSt
  have hStein : D = A2 * D * A2ᵀ + St := by
    have e1 : c2 ^ 2 • P2 = A2 * (c2 ^ 2 • P2) * A2ᵀ + c2 ^ 2 • E := by
      conv_lhs => rw [L2]
      rw [smul_add, Matrix.mul_smul, Matrix.smul_mul]
    have e2 : c1 ^ 2 • P1 = A1 * (c1 ^ 2 • P1) * A1ᵀ + c1 ^ 2 • E := by
      conv_lhs => rw [L1]
      rw [smul_add, Matrix.mul_smul, Matrix.smul_mul]
    rw [hD, hSt, mul_sub, sub_mul, sub_smul]
    conv_lhs => rw [e1, e2]
    abel
  have L1' : P1 = a ^ 2 • P1 + (a * c1) • (W * P1 + P1 * Wᵀ) + c1 ^ 2 • (W * P1 * Wᵀ) + E := by
    conv_lhs => rw [L1]
    rw [x1]
  have hS1 : St = c1 ^ 2 • ((a * (c2 - c1)) • (W * P1 + P1 * Wᵀ) +
      (c2 ^ 2 - c1 ^ 2) • (W * P1 * Wᵀ)) + (c2 ^ 2 - c1 ^ 2) • E := by
    rw [hSt, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, x1, x2]
    module
  have hS2 : St - (c2 - c1) ^ 2 • E = ((c2 - c1) * c1) • ((1 - a ^ 2) • P1 + c1 ^ 2 • (W * P1 * Wᵀ) + E)
      + ((c2 - c1) ^ 2 * c1 ^ 2) • (W * P1 * Wᵀ) := by
    linear_combination (norm := module) hS1 - ((c2 - c1) * c1) • L1'
  have hWP : (W * P1 * Wᵀ).PosSemidef := psd_congr hP1 W
  have ha2 : 0 ≤ 1 - a ^ 2 := by nlinarith [abs_nonneg a, sq_abs a]
  have hδ : 0 ≤ c2 - c1 := sub_nonneg.mpr h12
  have hS2psd : (St - (c2 - c1) ^ 2 • E).PosSemidef := by
    rw [hS2]
    exact ((((hP1.smul ha2).add (hWP.smul (sq_nonneg c1))).add hE.posSemidef).smul
      (mul_nonneg hδ h1)).add (hWP.smul (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hStpsd : St.PosSemidef := by
    have := hS2psd.add (hE.posSemidef.smul (sq_nonneg (c2 - c1)))
    simpa using this
  have hDpsd : D.PosSemidef :=
    stein_psd hE hStpsd hStein rfl (hP2.smul (sq_nonneg c2)) (hP1.smul (sq_nonneg c1)) hs2
  have : D - (c2 - c1) ^ 2 • E = A2 * D * A2ᵀ + (St - (c2 - c1) ^ 2 • E) := by
    conv_lhs => rw [hStein]
    abel
  rw [this]
  exact (psd_congr hDpsd A2).add hS2psd

lemma add_mem_Bpi {S : Finset (Fin n)} {B1 B2 : Matrix (Fin n) (Fin n) ℝ} (h1 : B1 ∈ Bpi S)
    (h2 : B2 ∈ Bpi S) : B1 + B2 ∈ Bpi S := fun i j h => by simp [h1 i j h, h2 i j h]

lemma sub_mem_Bpi {S : Finset (Fin n)} {B1 B2 : Matrix (Fin n) (Fin n) ℝ} (h1 : B1 ∈ Bpi S)
    (h2 : B2 ∈ Bpi S) : B1 - B2 ∈ Bpi S := fun i j h => by simp [h1 i j h, h2 i j h]

lemma smul_one_mem_Bpi (S : Finset (Fin n)) (a : ℝ) :
    a • (1 : Matrix (Fin n) (Fin n) ℝ) ∈ Bpi S := by
  intro i j h
  have hij : i ≠ j := by rintro rfl; exact h Iff.rfl
  simp [one_apply_ne hij]

/-- General comparison of the objective at two parameters: if `A₁ - B'' = s (A₂ - B)` and
`P₂ ⪰ s² P₁`, then `f₁(B'') ≤ f₂(B)`; strictly if moreover `P₂ - s² P₁ ⪰ κ E` with `κ > 0` and
`A₂ - B` has a nonzero entry. -/
theorem fval_compare {E P1 P2 A1 A2 B B'' : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    (hP1 : P1.PosSemidef) {s : ℝ} (hC : A1 - B'' = s • (A2 - B))
    (hQ : (P2 - s ^ 2 • P1).PosSemidef) :
    fval E P1 A1 B'' ≤ fval E P2 A2 B ∧
    (∀ κ : ℝ, 0 < κ → (P2 - s ^ 2 • P1 - κ • E).PosSemidef → ∀ a b, (A2 - B) a b ≠ 0 →
      fval E P1 A1 B'' < fval E P2 A2 B) := by
  set C0 := A2 - B with hC0
  set R1 := E + (s • C0) * P1 * (s • C0)ᵀ with hR1
  set R2 := E + C0 * P2 * C0ᵀ with hR2
  have hR1pd : R1.PosDef := hE.add_posSemidef (psd_congr hP1 _)
  have hsum : R1 + C0 * (P2 - s ^ 2 • P1) * C0ᵀ = R2 := by
    rw [hR1, hR2]
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_sub, sub_mul, sq]
    abel
  have key := det_add_psd hR1pd (psd_congr hQ C0)
  rw [hsum] at key
  have hfv1 : fval E P1 A1 B'' = Real.log (det R1) - Real.log (det E) := by rw [fval, hC]
  have hfv2 : fval E P2 A2 B = Real.log (det R2) - Real.log (det E) := by rw [fval]
  refine ⟨?_, ?_⟩
  · rw [hfv1, hfv2]
    have := Real.log_le_log hR1pd.det_pos key.1
    linarith
  · intro κ hκ hdom' a b hab
    have hdom : (C0 * (P2 - s ^ 2 • P1) * C0ᵀ - κ • (C0 * E * C0ᵀ)).PosSemidef := by
      have h3 : C0 * (P2 - s ^ 2 • P1) * C0ᵀ - κ • (C0 * E * C0ᵀ) =
          C0 * (P2 - s ^ 2 • P1 - κ • E) * C0ᵀ := by
        simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [h3]; exact psd_congr hdom' C0
    have hrow : (fun k => C0 a k) ≠ 0 := fun h => hab (congrFun h b)
    have hdiag : 0 < (C0 * E * C0ᵀ) a a := by
      have := hE.2 (fun k => C0 a k) hrow
      convert this using 1
      simp only [mul_apply, transpose_apply, dotProduct, mulVec, star_trivial, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    have hdiag2 : 0 ≤ (C0 * (P2 - s ^ 2 • P1) * C0ᵀ - κ • (C0 * E * C0ᵀ)) a a := by
      have := hdom.2 (Pi.single a 1)
      simpa [dotProduct, mulVec, Pi.single_apply] using this
    have hne : C0 * (P2 - s ^ 2 • P1) * C0ᵀ ≠ 0 := by
      intro h0
      rw [h0, zero_sub, neg_apply, smul_apply, smul_eq_mul] at hdiag2
      have : 0 < κ * (C0 * E * C0ᵀ) a a := mul_pos hκ hdiag
      linarith
    rw [hfv1, hfv2]
    have := Real.log_lt_log hR1pd.det_pos (key.2 hne)
    linarith

/-- `J(A(c), E)`, with the stationary covariance `P(c)` of `A(c) = aI + cW`. -/
noncomputable def Jb (a : ℝ) (W E : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : ℝ :=
  J E (Pser (Acoup a c W) E) (Acoup a c W)

/-- The parameter domain of part (b): `c ≥ 0` with a convergent covariance series for `A(c)`.
It contains `𝒞 = {c ≥ 0 : spr(A(c)) < 1}`. -/
def DomB (a : ℝ) (W E : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {c | 0 ≤ c ∧ SerSummable (Acoup a c W) E}

/-- Comparison of covariances along `c` (from `Qb_mono`). -/
lemma Pb_compare {a : ℝ} (ha : |a| ≤ 1) {W E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    {c1 c2 : ℝ} (h1 : 0 ≤ c1) (h12 : c1 ≤ c2)
    (hs1 : SerSummable (Acoup a c1 W) E) (hs2 : SerSummable (Acoup a c2 W) E) :
    (Pser (Acoup a c2 W) E - (c1 / c2) ^ 2 • Pser (Acoup a c1 W) E).PosSemidef ∧
    (0 < c2 → (Pser (Acoup a c2 W) E - (c1 / c2) ^ 2 • Pser (Acoup a c1 W) E -
      ((c2 - c1) / c2) ^ 2 • E).PosSemidef) := by
  have hG := Qb_mono ha hE h1 h12 hs1 hs2
  set P1 := Pser (Acoup a c1 W) E
  set P2 := Pser (Acoup a c2 W) E
  have hP2 := Pser_psd hE hs2
  have hpos : 0 < c2 → (P2 - (c1 / c2) ^ 2 • P1 - ((c2 - c1) / c2) ^ 2 • E).PosSemidef := by
    intro hc2
    have hc2' : c2 ^ 2 ≠ 0 := by positivity
    have e : P2 - (c1 / c2) ^ 2 • P1 - ((c2 - c1) / c2) ^ 2 • E =
        (c2 ^ 2)⁻¹ • (c2 ^ 2 • P2 - c1 ^ 2 • P1 - (c2 - c1) ^ 2 • E) := by
      rw [smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, inv_mul_cancel₀ hc2', one_smul,
        div_pow, div_pow, div_eq_inv_mul, div_eq_inv_mul]
    rw [e]; exact hG.smul (by positivity)
  refine ⟨?_, hpos⟩
  rcases eq_or_lt_of_le (h1.trans h12) with h | h
  · rw [← h, div_zero]; simpa using hP2
  · have := (hpos h).add (hE.posSemidef.smul (sq_nonneg ((c2 - c1) / c2)))
    simpa using this

lemma Acoup_compare (a : ℝ) (W B : Matrix (Fin n) (Fin n) ℝ) {c1 c2 : ℝ} (h1 : 0 ≤ c1)
    (h12 : c1 ≤ c2) :
    Acoup a c1 W - (a • 1 + (c1 / c2) • (B - a • 1)) = (c1 / c2) • (Acoup a c2 W - B) := by
  have hsc : c1 / c2 * c2 = c1 := by
    rcases eq_or_lt_of_le (h1.trans h12) with h | h
    · have : c1 = 0 := le_antisymm (h ▸ h12) h1
      rw [← h, this]; simp
    · exact div_mul_cancel₀ c1 h.ne'
  unfold Acoup
  simp only [smul_sub, smul_add, smul_smul]
  rw [hsc]
  module

/-- Part (b), monotonicity of `c ↦ J(A(c), E)`. -/
theorem Jb_mono {a : ℝ} (ha : |a| ≤ 1) {W E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    {c1 c2 : ℝ} (h1 : 0 ≤ c1) (h12 : c1 ≤ c2)
    (hs1 : SerSummable (Acoup a c1 W) E) (hs2 : SerSummable (Acoup a c2 W) E) :
    Jb a W E c1 ≤ Jb a W E c2 := by
  have hP1 := Pser_psd hE hs1
  have hPs := (Pb_compare ha hE h1 h12 hs1 hs2).1
  unfold Jb J
  apply ciInf_mono (Set.finite_range _).bddBelow
  intro S
  apply le_JS
  intro B hB
  have hB'' : a • 1 + (c1 / c2) • (B - a • 1) ∈ Bpi S.1 :=
    add_mem_Bpi (smul_one_mem_Bpi _ a) (smul_mem_Bpi (sub_mem_Bpi hB (smul_one_mem_Bpi _ a)) _)
  calc JS E (Pser (Acoup a c1 W) E) (Acoup a c1 W) S.1
      ≤ fval E (Pser (Acoup a c1 W) E) (Acoup a c1 W) (a • 1 + (c1 / c2) • (B - a • 1)) / 2 :=
        JS_le hE hP1 hB''
    _ ≤ fval E (Pser (Acoup a c2 W) E) (Acoup a c2 W) B / 2 := by
        have := (fval_compare hE hP1 (Acoup_compare a W B h1 h12) hPs).1
        linarith

lemma serSummable_zero {a : ℝ} (ha : |a| < 1) (W E : Matrix (Fin n) (Fin n) ℝ) :
    SerSummable (Acoup a 0 W) E := by
  unfold SerSummable Acoup
  have hr0 : 0 ≤ a ^ 2 := sq_nonneg a
  have hr1 : a ^ 2 < 1 := by nlinarith [abs_nonneg a, sq_abs a, abs_lt.mp ha]
  have := (summable_geometric_of_lt_one hr0 hr1).smul_const E
  convert this using 1
  funext j
  simp only [zero_smul, add_zero, smul_pow, one_pow, transpose_smul, transpose_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [← mul_pow, sq]

/-- Part (b), value at `c = 0`: `J(aI, E) = 0`. -/
theorem Jb_zero {a : ℝ} (ha : |a| < 1) {W E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) :
    Jb a W E 0 = 0 := by
  have hP0 := Pser_psd hE (serSummable_zero ha W E)
  unfold Jb J
  have h : ∀ S : Bip n, JS E (Pser (Acoup a 0 W) E) (Acoup a 0 W) S.1 = 0 := by
    intro S
    apply IsLeast.csInf_eq
    refine ⟨⟨Acoup a 0 W, ?_, ?_⟩, ?_⟩
    · have : Acoup a 0 W = a • (1 : Matrix (Fin n) (Fin n) ℝ) := by simp [Acoup]
      rw [this]; exact smul_one_mem_Bpi _ a
    · simp [fval]
    · rintro _ ⟨B, -, rfl⟩
      exact div_nonneg (fval_nonneg hE hP0 _ B) zero_le_two
  simp only [h]
  exact Real.iInf_const_zero

/-- Part (b), strictness for connected support of `W`. -/
theorem Jb_strictMono {a : ℝ} (ha : |a| ≤ 1) {W E : Matrix (Fin n) (Fin n) ℝ} (hn : 2 ≤ n)
    (hE : E.PosDef) (hW : (supportGraph W).Connected) {c1 c2 : ℝ} (h1 : 0 ≤ c1) (h12 : c1 < c2)
    (hs1 : SerSummable (Acoup a c1 W) E) (hs2 : SerSummable (Acoup a c2 W) E) :
    Jb a W E c1 < Jb a W E c2 := by
  have hc2 : 0 < c2 := h1.trans_lt h12
  have hP1 := Pser_psd hE hs1
  have hcmp := Pb_compare ha hE h1 h12.le hs1 hs2
  haveI : Nonempty (Bip n) := bip_nonempty hn
  obtain ⟨S0, hS0⟩ := exists_eq_ciInf_of_finite
    (f := fun S : Bip n => JS E (Pser (Acoup a c2 W) E) (Acoup a c2 W) S.1)
  unfold Jb J
  rw [← hS0]
  refine lt_of_le_of_lt (ciInf_le (Set.finite_range _).bddBelow S0) ?_
  have hP2 : (Pser (Acoup a c2 W) E).PosDef := Pser_posDef hE hs2
  obtain ⟨Bs, hBs, hmin⟩ := exists_minimizer hE hP2 (Acoup a c2 W) S0.1
  have hJS2 : JS E (Pser (Acoup a c2 W) E) (Acoup a c2 W) S0.1 =
      fval E (Pser (Acoup a c2 W) E) (Acoup a c2 W) Bs / 2 := by
    apply IsLeast.csInf_eq
    refine ⟨⟨Bs, hBs, rfl⟩, ?_⟩
    rintro _ ⟨B, hB, rfl⟩
    have := hmin B hB
    show fval E (Pser (Acoup a c2 W) E) (Acoup a c2 W) Bs / 2 ≤
      fval E (Pser (Acoup a c2 W) E) (Acoup a c2 W) B / 2
    linarith
  rw [hJS2]
  obtain ⟨i, j, hcross, hWij⟩ : ∃ i j, ¬ (i ∈ S0.1 ↔ j ∈ S0.1) ∧ W i j ≠ 0 := by
    have := not_mem_Bpi_of_connected hW S0.2
    simp only [Bpi, Set.mem_setOf_eq, not_forall] at this
    obtain ⟨i, j, h, h'⟩ := this
    exact ⟨i, j, h, h'⟩
  have hij : i ≠ j := by rintro rfl; exact hcross Iff.rfl
  have hC : (Acoup a c2 W - Bs) i j ≠ 0 := by
    simp only [Acoup, sub_apply, add_apply, smul_apply, one_apply_ne hij, hBs i j hcross,
      smul_eq_mul, mul_zero, zero_add, sub_zero]
    exact mul_ne_zero hc2.ne' hWij
  have hB'' : a • 1 + (c1 / c2) • (Bs - a • 1) ∈ Bpi S0.1 :=
    add_mem_Bpi (smul_one_mem_Bpi _ a) (smul_mem_Bpi (sub_mem_Bpi hBs (smul_one_mem_Bpi _ a)) _)
  have hκ : 0 < ((c2 - c1) / c2) ^ 2 := by
    have : 0 < (c2 - c1) / c2 := div_pos (sub_pos.mpr h12) hc2
    positivity
  calc JS E (Pser (Acoup a c1 W) E) (Acoup a c1 W) S0.1
      ≤ fval E (Pser (Acoup a c1 W) E) (Acoup a c1 W) (a • 1 + (c1 / c2) • (Bs - a • 1)) / 2 :=
        JS_le hE hP1 hB''
    _ < fval E (Pser (Acoup a c2 W) E) (Acoup a c2 W) Bs / 2 := by
        have := (fval_compare hE hP1 (Acoup_compare a W Bs h1 h12.le) hcmp.1).2 _ hκ
          (hcmp.2 hc2) i j hC
        linarith

/-! ## Proposition `prop:scaling`, part (b), packaged -/

/-- **Proposition (scaling), part (b), monotonicity.** For `|a| ≤ 1` (in particular `|a| < 1`)
and `E ≻ 0`, `c ↦ J(aI + cW, E)` is nondecreasing on `DomB a W E`. -/
theorem prop_scaling_b_monotone {a : ℝ} (ha : |a| ≤ 1) {W E : Matrix (Fin n) (Fin n) ℝ}
    (hE : E.PosDef) : MonotoneOn (Jb a W E) (DomB a W E) :=
  fun _ hc1 _ hc2 h12 => Jb_mono ha hE hc1.1 h12 hc1.2 hc2.2

/-- **Proposition (scaling), part (b), value at `0`.** For `|a| < 1`, `0 ∈ DomB a W E` and
`J(aI, E) = 0`. -/
theorem prop_scaling_b_zero {a : ℝ} (ha : |a| < 1) {W E : Matrix (Fin n) (Fin n) ℝ}
    (hE : E.PosDef) : 0 ∈ DomB a W E ∧ Jb a W E 0 = 0 :=
  ⟨⟨le_rfl, serSummable_zero ha W E⟩, Jb_zero ha hE⟩

/-- **Proposition (scaling), part (b), strictness.** For `n ≥ 2`, `|a| ≤ 1`, `E ≻ 0` and `W`
with connected undirected off-diagonal support, `c ↦ J(aI + cW, E)` is strictly increasing on
`DomB a W E`. (The zero-diagonal hypothesis on `W` is not needed for this statement.) -/
theorem prop_scaling_b_strictMono {a : ℝ} (ha : |a| ≤ 1) {W E : Matrix (Fin n) (Fin n) ℝ}
    (hn : 2 ≤ n) (hE : E.PosDef) (hW : (supportGraph W).Connected) :
    StrictMonoOn (Jb a W E) (DomB a W E) :=
  fun _ hc1 _ hc2 h12 => Jb_strictMono ha hn hE hW hc1.1 h12 hc1.2 hc2.2


/-- Non-vacuity of part (b): for `n = 2`, `a = 0`, `E = 1` and `W = !![0, 1; 0, 0]` (zero
diagonal, connected support), every `c ≥ 0` lies in the domain, so `c ↦ J(cW, 1)` is strictly
increasing on `[0, ∞)`. -/
example : StrictMonoOn (Jb 0 !![(0 : ℝ), 1; 0, 0] 1) (Set.Ici 0) := by
  set W : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0] with hWdef
  have hW2 : W ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [W, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hsum : ∀ c, SerSummable (Acoup 0 c W) 1 := by
    intro c
    unfold SerSummable
    apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro j hj
    have : 2 ≤ j := by simpa using hj
    have hA : Acoup 0 c W = c • W := by simp [Acoup]
    rw [hA, smul_pow, pow_eq_zero_of_le this hW2]
    simp
  have hconn : (supportGraph W).Connected := by
    have hadj : (supportGraph W).Adj 0 1 := by simp [supportGraph, SimpleGraph.fromRel_adj, W]
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ⟨0⟩⟩
    fin_cases u <;> fin_cases v
    exacts [SimpleGraph.Reachable.refl _, hadj.reachable, hadj.symm.reachable,
      SimpleGraph.Reachable.refl _]
  have h := prop_scaling_b_strictMono (a := 0) (by norm_num) (by norm_num) PosDef.one hconn
  intro c1 hc1 c2 hc2 h12
  exact h ⟨hc1, hsum c1⟩ ⟨hc2, hsum c2⟩ h12

/-- Step (4) of the proof: for `t ≠ 0` the support of `tA` is that of `A`. -/
theorem supportGraph_smul (A : Matrix (Fin n) (Fin n) ℝ) {t : ℝ} (ht : t ≠ 0) :
    supportGraph (t • A) = supportGraph A := by
  ext i j
  simp [supportGraph, SimpleGraph.fromRel_adj, ht]

/-- For `c ≠ 0` the off-diagonal support of `aI + cW` is that of `W`. -/
theorem supportGraph_Acoup (a : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) {c : ℝ} (hc : c ≠ 0) :
    supportGraph (Acoup a c W) = supportGraph W := by
  ext i j
  simp only [supportGraph, SimpleGraph.fromRel_adj, Acoup]
  constructor
  · rintro ⟨hij, h⟩
    refine ⟨hij, ?_⟩
    have hji : j ≠ i := fun h' => hij h'.symm
    simpa [one_apply_ne hij, one_apply_ne hji, hc] using h
  · rintro ⟨hij, h⟩
    refine ⟨hij, ?_⟩
    have hji : j ≠ i := fun h' => hij h'.symm
    simpa [one_apply_ne hij, one_apply_ne hji, hc] using h


/-- Step (2) of the proof: with `B = t B'`, the objective at `tA` is the residual `R_t(B')`. -/
lemma fval_eq_Rt (A E B' : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    fval E (Pt A E t) (t • A) (t • B') = Real.log (det (Rt A E B' t)) - Real.log (det E) := by
  unfold fval Rt
  rw [← smul_sub]
  simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]

/-- Step (2): for `t ≠ 0`, `B' ↦ tB'` is a bijection of `𝔅_π`, so
`J_π(tA, E) = inf_{B' ∈ 𝔅_π} ½ (log det R_t(B') - log det E)`. -/
theorem JS_eq_Rt (A E : Matrix (Fin n) (Fin n) ℝ) {t : ℝ} (ht : t ≠ 0) (S : Finset (Fin n)) :
    JS E (Pt A E t) (t • A) S =
      sInf ((fun B' => (Real.log (det (Rt A E B' t)) - Real.log (det E)) / 2) '' Bpi S) := by
  unfold JS
  congr 1
  ext v
  constructor
  · rintro ⟨B, hB, rfl⟩
    refine ⟨t⁻¹ • B, smul_mem_Bpi hB _, ?_⟩
    show (Real.log (det (Rt A E (t⁻¹ • B) t)) - Real.log (det E)) / 2 =
      fval E (Pt A E t) (t • A) B / 2
    rw [← fval_eq_Rt, smul_smul, mul_inv_cancel₀ ht, one_smul]
  · rintro ⟨B', hB', rfl⟩
    refine ⟨t • B', smul_mem_Bpi hB' _, ?_⟩
    show fval E (Pt A E t) (t • A) (t • B') / 2 =
      (Real.log (det (Rt A E B' t)) - Real.log (det E)) / 2
    rw [fval_eq_Rt]


/-! ## From the spectral radius to the covariance series -/

/-- Spectral radius of a real matrix: the spectral radius of its complexification
(the largest modulus of a complex eigenvalue). -/
noncomputable def spr (M : Matrix (Fin n) (Fin n) ℝ) : ENNReal :=
  spectralRadius ℂ (M.map (algebraMap ℝ ℂ))

/-- Homogeneity of the spectral radius: `spr(tA) = t · spr(A)` for `t ≥ 0`. -/
lemma spr_smul (A : Matrix (Fin n) (Fin n) ℝ) {t : ℝ} (ht : 0 ≤ t) :
    spr (t • A) = ENNReal.ofReal t * spr A := by
  unfold spr
  have hmap : (t • A).map (algebraMap ℝ ℂ) = (t : ℂ) • A.map (algebraMap ℝ ℂ) := by
    ext i j; simp
  rw [hmap]
  rcases eq_or_lt_of_le ht with h0 | hpos
  · rw [← h0]; simp
  · set X := A.map (algebraMap ℝ ℂ)
    have hne : (t : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hsmul : (t : ℂ) • X = (Units.mk0 (t : ℂ) hne) • X := rfl
    rw [hsmul, spectralRadius, spectralRadius, spectrum.unit_smul_eq_smul, ← Set.image_smul,
      iSup_image, ENNReal.mul_iSup]
    refine iSup_congr fun k => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun _ => ?_
    rw [Units.smul_def, Units.val_mk0, smul_eq_mul, nnnorm_mul, ENNReal.coe_mul]
    congr 1
    rw [ENNReal.ofReal, Complex.nnnorm_real]
    congr 1
    rw [Real.nnnorm_of_nonneg ht, Real.toNNReal_of_nonneg ht]

/-- The paper's range `t ∈ [0, 1/spr(A))` (all `t ≥ 0` if `spr(A) = 0`), written multiplicatively,
is `{t ≥ 0 : spr(tA) < 1}`. -/
lemma spr_range_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    {t : ℝ | 0 ≤ t ∧ spr (t • A) < 1} = {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t * spr A < 1} := by
  ext t
  constructor
  · rintro ⟨ht, h⟩; exact ⟨ht, by rwa [spr_smul A ht] at h⟩
  · rintro ⟨ht, h⟩; exact ⟨ht, by rwa [spr_smul A ht]⟩

section linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
open Filter Topology

lemma entry_le_norm (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖X i j‖ ≤ ‖X‖ := by
  have : ‖X i j‖₊ ≤ ‖X‖₊ := by
    rw [Matrix.linfty_opNNNorm_def X]
    calc ‖X i j‖₊ ≤ ∑ k, ‖X i k‖₊ :=
          Finset.single_le_sum (f := fun k => ‖X i k‖₊) (fun _ _ => zero_le _) (Finset.mem_univ j)
      _ ≤ Finset.univ.sup fun i => ∑ k, ‖X i k‖₊ :=
          Finset.le_sup (f := fun i => ∑ k, ‖X i k‖₊) (Finset.mem_univ i)
  exact_mod_cast this

/-- `spr(M) < 1` (complex spectral radius) gives convergence of `∑_j M^j E (M^j)ᵀ`. -/
theorem serSummable_of_spr_lt_one {M : Matrix (Fin n) (Fin n) ℝ} (E : Matrix (Fin n) (Fin n) ℝ)
    (h : spr M < 1) : SerSummable M E := by
  set X : Matrix (Fin n) (Fin n) ℂ := M.map (algebraMap ℝ ℂ) with hX
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  have hG := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius X
  obtain ⟨c, hc1, hc2⟩ := exists_between h
  have hctop : c ≠ ⊤ := ne_top_of_lt hc2
  set r := c.toReal with hr
  have hrc : ENNReal.ofReal r = c := ENNReal.ofReal_toReal hctop
  have hr1 : r < 1 := by
    have := (ENNReal.toReal_lt_toReal hctop ENNReal.one_ne_top).mpr hc2
    simpa using this
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hev : ∀ᶠ k : ℕ in atTop, ‖X ^ k‖ ≤ r ^ k := by
    have h1 : ∀ᶠ k : ℕ in atTop, ENNReal.ofReal (‖X ^ k‖ ^ (1 / k : ℝ)) < ENNReal.ofReal r := by
      rw [hrc]; exact hG.eventually (gt_mem_nhds hc1)
    filter_upwards [h1, eventually_ge_atTop 1] with k hk hk1
    have hrpos : 0 < r := by
      rcases eq_or_lt_of_le hr0 with h0 | h0
      · rw [← h0, ENNReal.ofReal_zero] at hk; exact absurd hk (not_lt_zero')
      · exact h0
    have hlt : ‖X ^ k‖ ^ (1 / k : ℝ) < r := (ENNReal.ofReal_lt_ofReal_iff hrpos).mp hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hpow : ‖X ^ k‖ = (‖X ^ k‖ ^ (1 / k : ℝ)) ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hk0,
        Real.rpow_one]
    rw [hpow]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hlt.le k
  have hXk : ∀ k : ℕ, X ^ k = (M ^ k).map (algebraMap ℝ ℂ) := fun k => by
    have := map_pow (algebraMap ℝ ℂ).mapMatrix M k
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at this
    rw [hX, this]
  have hentry : ∀ (k : ℕ) (i j : Fin n), |(M ^ k) i j| ≤ ‖X ^ k‖ := by
    intro k i j
    rw [hXk k]
    have := entry_le_norm ((M ^ k).map (algebraMap ℝ ℂ)) i j
    simpa [Complex.norm_real] using this
  unfold SerSummable
  refine Pi.summable.mpr fun a => Pi.summable.mpr fun b => ?_
  set CE := ∑ c, ∑ d, |E c d| with hCE
  have hCE0 : 0 ≤ CE := Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun d _ => abs_nonneg _))
  have hT : ∀ k : ℕ, ‖(M ^ k * E * (M ^ k)ᵀ) a b‖ ≤ CE * ‖X ^ k‖ ^ 2 := by
    intro k
    have hexp : (M ^ k * E * (M ^ k)ᵀ) a b = ∑ c, ∑ d, (M ^ k) a c * E c d * (M ^ k) b d := by
      simp only [mul_apply, transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hexp, Real.norm_eq_abs]
    calc |∑ c, ∑ d, (M ^ k) a c * E c d * (M ^ k) b d|
        ≤ ∑ c, |∑ d, (M ^ k) a c * E c d * (M ^ k) b d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, ∑ d, |(M ^ k) a c * E c d * (M ^ k) b d| :=
          Finset.sum_le_sum (fun c _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ c, ∑ d, |E c d| * ‖X ^ k‖ ^ 2 := by
          apply Finset.sum_le_sum; intro c _; apply Finset.sum_le_sum; intro d _
          rw [abs_mul, abs_mul]
          have h1 := hentry k a c
          have h2 := hentry k b d
          calc |(M ^ k) a c| * |E c d| * |(M ^ k) b d| ≤ ‖X ^ k‖ * |E c d| * ‖X ^ k‖ := by
                gcongr
            _ = |E c d| * ‖X ^ k‖ ^ 2 := by ring
      _ = CE * ‖X ^ k‖ ^ 2 := by rw [hCE, Finset.sum_mul]; simp only [Finset.sum_mul]
  refine Summable.of_norm_bounded_eventually (g := fun k : ℕ => CE * (r ^ 2) ^ k)
    ((summable_geometric_of_lt_one (sq_nonneg r) (by nlinarith)).mul_left CE) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with k hk
  calc ‖(M ^ k * E * (M ^ k)ᵀ) a b‖ ≤ CE * ‖X ^ k‖ ^ 2 := hT k
    _ ≤ CE * (r ^ k) ^ 2 := by gcongr
    _ = CE * (r ^ 2) ^ k := by ring

/-- The spectral radius of a matrix is finite. -/
lemma spr_lt_top (M : Matrix (Fin n) (Fin n) ℝ) : spr M < ⊤ := by
  unfold spr
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · haveI : Subsingleton (Matrix (Fin n) (Fin n) ℂ) := inferInstance
    simp
  · haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
    haveI : NormOneClass (Matrix (Fin n) (Fin n) ℂ) := Matrix.linfty_opNormOneClass
    exact lt_of_le_of_lt (spectrum.spectralRadius_le_nnnorm _) ENNReal.coe_lt_top

/-- Non-vacuity of the paper's `𝒞` in part (b): for `|a| < 1` it contains `[0, ε)` for some
`ε > 0`. -/
lemma sprB_range_contains {a : ℝ} (ha : |a| < 1) (W : Matrix (Fin n) (Fin n) ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c, 0 ≤ c → c < ε → spr (Acoup a c W) < 1 := by
  set w := ‖W.map (algebraMap ℝ ℂ)‖ with hw
  have hw0 : 0 ≤ w := norm_nonneg _
  refine ⟨(1 - |a|) / (w + 1), div_pos (by linarith) (by linarith), fun c hc hcε => ?_⟩
  unfold spr
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · haveI : Subsingleton (Matrix (Fin n) (Fin n) ℂ) := inferInstance
    simp
  · haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
    haveI : NormOneClass (Matrix (Fin n) (Fin n) ℂ) := Matrix.linfty_opNormOneClass
    have hX : (Acoup a c W).map (algebraMap ℝ ℂ) =
        (a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (c : ℂ) • W.map (algebraMap ℝ ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Acoup]
      · simp [Acoup, one_apply_ne hij]
    have hnorm : ‖(Acoup a c W).map (algebraMap ℝ ℂ)‖ ≤ |a| + c * w := by
      rw [hX]
      calc ‖(a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (c : ℂ) • W.map (algebraMap ℝ ℂ)‖
          ≤ ‖(a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖(c : ℂ) • W.map (algebraMap ℝ ℂ)‖ :=
            norm_add_le _ _
        _ = |a| + c * w := by
            rw [norm_smul, norm_smul, norm_one, mul_one, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc]
    have hlt : |a| + c * w < 1 := by
      have h1 : c * (w + 1) < 1 - |a| := by
        rwa [lt_div_iff₀ (by linarith)] at hcε
      nlinarith
    calc spectralRadius ℂ ((Acoup a c W).map (algebraMap ℝ ℂ))
        ≤ ‖(Acoup a c W).map (algebraMap ℝ ℂ)‖₊ := spectrum.spectralRadius_le_nnnorm _
      _ = ENNReal.ofReal ‖(Acoup a c W).map (algebraMap ℝ ℂ)‖ := (ofReal_norm_eq_enorm _).symm
      _ < 1 := by rw [ENNReal.ofReal_lt_one]; linarith

end linfty

/-- Non-vacuity of the paper's range in part (a): it contains `[0, ε)` for some `ε > 0`. -/
lemma spr_range_contains (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 ≤ t → t < ε → ENNReal.ofReal t * spr A < 1 := by
  have htop := spr_lt_top A
  set s := (spr A).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hsA : spr A = ENNReal.ofReal s := (ENNReal.ofReal_toReal htop.ne).symm
  refine ⟨1 / (s + 1), by positivity, fun t ht htε => ?_⟩
  rw [hsA, ← ENNReal.ofReal_mul ht, ENNReal.ofReal_lt_one]
  have h1 : t * (s + 1) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at htε; linarith
  nlinarith

lemma summableAt_iff (A E : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    SummableAt A E t ↔ SerSummable (t • A) E := by
  unfold SummableAt SerSummable
  simp only [Pt_term]

/-- The paper's parameter range `{t ≥ 0 : spr(tA) < 1}` (i.e. `[0, 1/spr(A))`) lies in `Dom A E`. -/
lemma spr_subset_Dom (A E : Matrix (Fin n) (Fin n) ℝ) :
    {t : ℝ | 0 ≤ t ∧ spr (t • A) < 1} ⊆ Dom A E :=
  fun _ ht => ⟨ht.1, (summableAt_iff A E _).mpr (serSummable_of_spr_lt_one E ht.2)⟩

/-- The paper's `𝒞 = {c ≥ 0 : spr(aI + cW) < 1}` lies in `DomB a W E`. -/
lemma spr_subset_DomB (a : ℝ) (W E : Matrix (Fin n) (Fin n) ℝ) :
    {c : ℝ | 0 ≤ c ∧ spr (Acoup a c W) < 1} ⊆ DomB a W E :=
  fun _ hc => ⟨hc.1, serSummable_of_spr_lt_one E hc.2⟩

/-- **Proposition `prop:scaling` (a), with the paper's hypotheses.** Let `E ≻ 0`. On
`{t ≥ 0 : t · spr(A) < 1}` (that is, `t ∈ [0, 1/spr(A))`, all `t ≥ 0` if `spr(A) = 0`),
`t ↦ J(tA, E)` is nondecreasing, `J(0, E) = 0`, and if `n ≥ 2` and the undirected support of `A`
is connected it is strictly increasing. (The paper's extra assumption `spr(A) < 1` is not
needed.) -/
theorem prop_scaling_a {A E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) :
    MonotoneOn (Jt A E) {t | 0 ≤ t ∧ ENNReal.ofReal t * spr A < 1} ∧ Jt A E 0 = 0 ∧
    (2 ≤ n → (supportGraph A).Connected →
      StrictMonoOn (Jt A E) {t | 0 ≤ t ∧ ENNReal.ofReal t * spr A < 1}) := by
  rw [← spr_range_eq]
  exact ⟨(prop_scaling_a_monotone hE).mono (spr_subset_Dom A E), Jt_zero hE,
    fun hn hA => (prop_scaling_a_strictMono hn hE hA).mono (spr_subset_Dom A E)⟩

/-- **Proposition `prop:scaling` (b), with the paper's hypotheses.** Let `E ≻ 0`, `|a| < 1`,
`A(c) = aI + cW` and `𝒞 = {c ≥ 0 : spr(A(c)) < 1}`. Then `c ↦ J(A(c), E)` is nondecreasing on `𝒞`,
`J(A(0), E) = 0`, and if `n ≥ 2` and the undirected support of `W` is connected it is strictly
increasing on `𝒞`. (`W` of zero diagonal is not needed.) -/
theorem prop_scaling_b {a : ℝ} (ha : |a| < 1) {W E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) :
    MonotoneOn (Jb a W E) {c | 0 ≤ c ∧ spr (Acoup a c W) < 1} ∧ Jb a W E 0 = 0 ∧
    (2 ≤ n → (supportGraph W).Connected →
      StrictMonoOn (Jb a W E) {c | 0 ≤ c ∧ spr (Acoup a c W) < 1}) :=
  ⟨(prop_scaling_b_monotone ha.le hE).mono (spr_subset_DomB a W E), Jb_zero ha hE,
    fun hn hW => (prop_scaling_b_strictMono ha.le hn hE hW).mono (spr_subset_DomB a W E)⟩


/-! ## The minimum cut in a fixed representative -/

/-- `‖A_cross(π)‖_F²`: the squared Frobenius norm of the coefficients of `A` crossing `π`. -/
noncomputable def cutWeight (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i, ∑ j, if (i ∈ S ↔ j ∈ S) then 0 else A i j ^ 2

/-- The minimum cut `w_min = min_π ‖A_cross(π)‖_F²` of Theorem `thm:cheeger`. -/
noncomputable def wmin (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := ⨅ S : Bip n, cutWeight A S.1

lemma cutWeight_smul (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (S : Finset (Fin n)) :
    cutWeight (t • A) S = t ^ 2 * cutWeight A S := by
  unfold cutWeight
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [mul_pow]

lemma cutWeight_Acoup (a c : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    cutWeight (Acoup a c W) S = c ^ 2 * cutWeight W S := by
  unfold cutWeight
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · simp
  · have hij : i ≠ j := by rintro rfl; exact h Iff.rfl
    simp [Acoup, one_apply_ne hij, mul_pow]

/-- Remark of `prop:scaling`: the minimum cut of `tA` is `t² w_min(A)`. -/
theorem wmin_smul (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : wmin (t • A) = t ^ 2 * wmin A := by
  unfold wmin
  simp only [cutWeight_smul]
  exact (Real.mul_iInf_of_nonneg (sq_nonneg t) _).symm

/-- Remark of `prop:scaling`: the minimum cut of `aI + cW` is `c² w_min(W)`. -/
theorem wmin_Acoup (a c : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    wmin (Acoup a c W) = c ^ 2 * wmin W := by
  unfold wmin
  simp only [cutWeight_Acoup]
  exact (Real.mul_iInf_of_nonneg (sq_nonneg c) _).symm

end QAuditScaling

#print axioms QAuditScaling.Pt_mono
#print axioms QAuditScaling.sq_smul_Pt_mono
#print axioms QAuditScaling.resid_incr
#print axioms QAuditScaling.Pt_lyap
#print axioms QAuditScaling.JS_eq_Rt
#print axioms QAuditScaling.exists_minimizer
#print axioms QAuditScaling.dom_ordConnected
#print axioms QAuditScaling.prop_scaling_a_monotone
#print axioms QAuditScaling.prop_scaling_a_zero
#print axioms QAuditScaling.prop_scaling_a_strictMono
#print axioms QAuditScaling.supportGraph_smul
#print axioms QAuditScaling.Pser_lyap
#print axioms QAuditScaling.Qb_mono
#print axioms QAuditScaling.prop_scaling_b_monotone
#print axioms QAuditScaling.prop_scaling_b_zero
#print axioms QAuditScaling.prop_scaling_b_strictMono
#print axioms QAuditScaling.supportGraph_Acoup
#print axioms QAuditScaling.serSummable_of_spr_lt_one
#print axioms QAuditScaling.spr_smul
#print axioms QAuditScaling.spr_range_eq
#print axioms QAuditScaling.spr_lt_top
#print axioms QAuditScaling.spr_range_contains
#print axioms QAuditScaling.sprB_range_contains
#print axioms QAuditScaling.prop_scaling_a
#print axioms QAuditScaling.prop_scaling_b
#print axioms QAuditScaling.wmin_smul
#print axioms QAuditScaling.wmin_Acoup
