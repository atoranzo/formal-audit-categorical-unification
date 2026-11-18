import QAuditAnalytic.Scaling

/-!
# Audit of `QAuditAnalytic/Scaling.lean` (non-vacuity and junk-value checks)

Written separately from the other modules, which it does not modify.

1. `spr_one`, `spr_two`, `range_two`: `spr` is the genuine spectral radius on simple matrices, and
   the paper's range `{t ≥ 0 : t · spr(A) < 1}` for `A = 2·I` is exactly `[0, 1/2)` (so `spr` is
   not a degenerate constant and the range in `prop_scaling_a` is computed correctly).
2. `partA_nonvacuous`: the strict part of `prop_scaling_a` (paper range) applies to a
   non-nilpotent connected `A = !![1,1;1,1]` (spectral radius 2, so even the paper's extra
   assumption `spr(A) < 1` fails) and yields `0 = J(0) < J(t₁A) ` for some `t₁ > 0`.
3. `partB_nonvacuous`: the strict part of `prop_scaling_b` (paper set `𝒞`) applies with a nonzero
   self-coupling `a = 1/2` (the file's own example only covers `a = 0`).
4. `Jt_junk`, `not_summableAt_A1`, `not_monotone_on_Ici`: outside the summability domain Lean's
   `tsum` is `0` and `Jt` takes the junk value `0`; for `A = !![1,1;1,1]` the function `t ↦ Jt`
   is *not* monotone on `[0, ∞)`.  So the domain restriction in `prop_scaling_a` is essential,
   and the theorems are not true "by junk".
-/

open Matrix Filter Topology

namespace QAuditScaling.Audit

open QAuditScaling

/-! ### 1. `spr` is not degenerate -/

theorem spr_one : spr (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  unfold spr
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  exact spectrum.spectralRadius_one

theorem spr_two : spr ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 2 := by
  rw [spr_smul _ (by norm_num), spr_one, mul_one, ENNReal.ofReal_ofNat]

/-- For `A = 2·I` the paper's range `[0, 1/spr(A))` is `[0, 1/2)`. -/
theorem range_two :
    {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t * spr ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) < 1} =
      Set.Ico 0 (1 / 2) := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_Ico, spr_two]
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    have e : ENNReal.ofReal (t * 2) = ENNReal.ofReal t * 2 := by
      rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_ofNat]
    rw [← e, ENNReal.ofReal_lt_one] at h
    linarith
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    have e : ENNReal.ofReal (t * 2) = ENNReal.ofReal t * 2 := by
      rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_ofNat]
    rw [← e, ENNReal.ofReal_lt_one]
    linarith

/-! ### 2. Part (a) on the paper range, with a non-nilpotent connected `A` -/

/-- `A = !![1,1;1,1]`: connected support, spectral radius `2`. -/
def A1 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]

theorem A1_connected : (supportGraph A1).Connected := by
  have hadj : (supportGraph A1).Adj 0 1 := by simp [supportGraph, SimpleGraph.fromRel_adj, A1]
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, ⟨0⟩⟩
  fin_cases u <;> fin_cases v
  exacts [SimpleGraph.Reachable.refl _, hadj.reachable, hadj.symm.reachable,
    SimpleGraph.Reachable.refl _]

theorem partA_nonvacuous :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ENNReal.ofReal t₁ * spr A1 < 1 ∧ Jt A1 1 0 < Jt A1 1 t₁ ∧
      0 < Jt A1 1 t₁ := by
  obtain ⟨ε, hε, hspr⟩ := spr_range_contains A1
  obtain ⟨-, h0, hstrict⟩ :=
    prop_scaling_a (A := A1) (PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef)
  have hm0 : (0 : ℝ) ∈ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t * spr A1 < 1} :=
    ⟨le_rfl, hspr 0 le_rfl hε⟩
  have hm1 : ε / 2 ∈ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t * spr A1 < 1} :=
    ⟨by positivity, hspr _ (by positivity) (by linarith)⟩
  have hlt := hstrict (le_refl 2) A1_connected hm0 hm1 (by positivity)
  exact ⟨ε / 2, by positivity, hm1.2, hlt, h0 ▸ hlt⟩

/-! ### 3. Part (b) on the paper's `𝒞`, with nonzero self-coupling `a = 1/2` -/

def W0 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

theorem W0_connected : (supportGraph W0).Connected := by
  have hadj : (supportGraph W0).Adj 0 1 := by simp [supportGraph, SimpleGraph.fromRel_adj, W0]
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, ⟨0⟩⟩
  fin_cases u <;> fin_cases v
  exacts [SimpleGraph.Reachable.refl _, hadj.reachable, hadj.symm.reachable,
    SimpleGraph.Reachable.refl _]

theorem partB_nonvacuous :
    ∃ c₁ : ℝ, 0 < c₁ ∧ spr (Acoup (1 / 2) 0 W0) < 1 ∧ spr (Acoup (1 / 2) c₁ W0) < 1 ∧
      Jb (1 / 2) W0 1 0 < Jb (1 / 2) W0 1 c₁ ∧ 0 < Jb (1 / 2) W0 1 c₁ := by
  have ha : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  obtain ⟨ε, hε, hspr⟩ := sprB_range_contains ha W0
  obtain ⟨-, h0, hstrict⟩ :=
    prop_scaling_b ha (W := W0) (PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef)
  have hm0 : (0 : ℝ) ∈ {c : ℝ | 0 ≤ c ∧ spr (Acoup (1 / 2) c W0) < 1} :=
    ⟨le_rfl, hspr 0 le_rfl hε⟩
  have hm1 : ε / 2 ∈ {c : ℝ | 0 ≤ c ∧ spr (Acoup (1 / 2) c W0) < 1} :=
    ⟨by positivity, hspr _ (by positivity) (by linarith)⟩
  have hlt := hstrict (le_refl 2) W0_connected hm0 hm1 (by positivity)
  exact ⟨ε / 2, by positivity, hm0.2, hm1.2, hlt, h0 ▸ hlt⟩

/-! ### 4. Junk values outside the domain: the domain restriction is essential -/

variable {n : ℕ}

/-- With covariance `0`, every objective value is `0`, hence `J = 0`. -/
theorem J_zero_cov {E A : Matrix (Fin n) (Fin n) ℝ} : J E 0 A = 0 := by
  unfold J
  have h : ∀ S : Bip n, JS E 0 A S.1 = 0 := by
    intro S
    unfold JS
    have himg : ((fun B => fval E 0 A B / 2) '' Bpi S.1) = {0} := by
      have hc : (fun B => fval E 0 A B / 2) = fun _ => (0 : ℝ) := by
        funext B; simp [fval]
      rw [hc]
      exact Set.Nonempty.image_const (s := Bpi S.1) ⟨0, zero_mem_Bpi _⟩ 0
    rw [himg, csInf_singleton]
  simp only [h]
  exact Real.iInf_const_zero

/-- Outside the summability domain, `Pt = 0` (Lean's `tsum` convention), so `Jt = 0`. -/
theorem Jt_junk {A E : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (h : ¬ SummableAt A E t) :
    Jt A E t = 0 := by
  have hP : Pt A E t = 0 := tsum_eq_zero_of_not_summable h
  unfold Jt
  rw [hP]
  exact J_zero_cov

theorem A1_sq : A1 * A1 = (2 : ℝ) • A1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A1, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem A1_pow_succ (j : ℕ) : A1 ^ (j + 1) = (2 : ℝ) ^ j • A1 := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Matrix.smul_mul, A1_sq, smul_smul, pow_succ]

theorem A1_transpose : A1ᵀ = A1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A1]

/-- The covariance series of `A1` diverges at `t = 1` (its `(0,0)` entries are `≥ 2`). -/
theorem not_summableAt_A1 : ¬ SummableAt A1 1 1 := by
  intro hs
  set f : ℕ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun j => (1 : ℝ) ^ (2 * j) • (A1 ^ j * 1 * (A1 ^ j)ᵀ) with hf
  have hs' : Summable f := hs
  have ht := hs'.tendsto_atTop_zero
  have hc : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0 :=
    (continuous_apply 0).comp (continuous_apply 0)
  have h00 : Tendsto (fun j => f j 0 0) atTop (𝓝 0) := by
    have := (hc.tendsto 0).comp ht
    simpa [Function.comp_def] using this
  have hA00 : A1 0 0 = 1 := by simp [A1]
  have hge : ∀ j : ℕ, 2 ≤ f (j + 1) 0 0 := by
    intro j
    simp only [hf]
    rw [A1_pow_succ, one_pow, one_smul, Matrix.mul_one, transpose_smul, A1_transpose,
      Matrix.smul_mul, Matrix.mul_smul, A1_sq, smul_smul, smul_smul, smul_apply, smul_eq_mul,
      hA00]
    have : (1 : ℝ) ≤ 2 ^ j * 2 ^ j := one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
    nlinarith
  have hev := (h00.comp (tendsto_add_atTop_nat 1)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨j, hj⟩ := hev.exists
  have := hge j
  simp only [Function.comp_apply] at hj
  linarith

/-- Hence `t ↦ Jt A1 1 t` is **not** monotone on `[0, ∞)`: the restriction of
`prop_scaling_a` to the summability domain (or to the paper range) is not decorative. -/
theorem not_monotone_on_Ici : ¬ MonotoneOn (Jt A1 1) (Set.Ici 0) := by
  intro hmono
  obtain ⟨t₁, ht₁, hrange, -, hpos⟩ := partA_nonvacuous
  have hJ1 : Jt A1 1 1 = 0 := Jt_junk not_summableAt_A1
  have ht₁1 : t₁ ≤ 1 := by
    -- `t₁` lies in the summability domain, `1` does not, and the domain is downward closed.
    by_contra hlt
    push_neg at hlt
    have hs : SummableAt A1 1 t₁ := ((spr_subset_Dom A1 1) ⟨ht₁.le, by
      rwa [spr_smul A1 ht₁.le]⟩).2
    exact not_summableAt_A1 (summableAt_mono zero_le_one hlt.le hs)
  have := hmono (Set.mem_Ici.mpr ht₁.le) (Set.mem_Ici.mpr zero_le_one) ht₁1
  linarith

end QAuditScaling.Audit

#print axioms QAuditScaling.Audit.spr_one
#print axioms QAuditScaling.Audit.range_two
#print axioms QAuditScaling.Audit.partA_nonvacuous
#print axioms QAuditScaling.Audit.partB_nonvacuous
#print axioms QAuditScaling.Audit.Jt_junk
#print axioms QAuditScaling.Audit.not_summableAt_A1
#print axioms QAuditScaling.Audit.not_monotone_on_Ici
