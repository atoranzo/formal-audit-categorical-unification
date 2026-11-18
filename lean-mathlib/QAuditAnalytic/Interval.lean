import QAuditAnalytic.Scaling

/-!
# Audit: the parameter set `𝒞` of Proposition `prop:scaling` (b) is an interval

Written separately from the other modules, which it does not modify.

The paper states that `𝒞 = {c ≥ 0 : spr(aI + cW) < 1}` is "an interval containing 0 (each
eigenvalue `a + cμ` of `A(c)` has `|a + cμ|` convex in `c`)".  `Scaling.lean` proves only that
`𝒞` contains some `[0, ε)` (`sprB_range_contains`).  Here the interval property is checked, with
the paper's argument: every eigenvalue of `aI + cW` (`c ≠ 0`) is `a + cμ` with `μ` an eigenvalue
of `W`, every such `a + cμ` is an eigenvalue of `aI + cW`, and `c ↦ |a + cμ|` is convex.
-/

open Matrix

namespace QAuditScaling.AuditInterval

open QAuditScaling

variable {n : ℕ}

lemma map_Acoup (a c : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    (Acoup a c W).map (algebraMap ℝ ℂ) =
      algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (a : ℂ) + (c : ℂ) • W.map (algebraMap ℝ ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Acoup, algebraMap_matrix_apply]
  · simp [Acoup, one_apply_ne hij, algebraMap_matrix_apply, hij]

lemma smul_mem_spec {c : ℝ} (hc : c ≠ 0) {X : Matrix (Fin n) (Fin n) ℂ} {s : ℂ} :
    (c : ℂ) * s ∈ spectrum ℂ ((c : ℂ) • X) ↔ s ∈ spectrum ℂ X := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have := spectrum.smul_mem_smul_iff (a := X) (s := s) (r := Units.mk0 (c : ℂ) hc')
  simpa [Units.smul_def] using this

/-- `μ ∈ σ(W) ⇒ cμ + a ∈ σ(aI + cW)`, for every `c` (at least one unit). -/
lemma mem_spec_Acoup [Nonempty (Fin n)] (a c : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (W.map (algebraMap ℝ ℂ))) :
    (c : ℂ) * μ + (a : ℂ) ∈ spectrum ℂ ((Acoup a c W).map (algebraMap ℝ ℂ)) := by
  rw [map_Acoup, spectrum.add_mem_add_iff]
  rcases eq_or_ne c 0 with h | h
  · subst h
    simp only [Complex.ofReal_zero, zero_mul, zero_smul]
    rw [spectrum.zero_eq]
    exact Set.mem_singleton 0
  · exact (smul_mem_spec h).mpr hμ

/-- For `c ≠ 0`, every eigenvalue of `aI + cW` is `cμ + a` with `μ ∈ σ(W)`. -/
lemma exists_of_mem_spec_Acoup (a : ℝ) {c : ℝ} (hc : c ≠ 0) (W : Matrix (Fin n) (Fin n) ℝ)
    {l : ℂ} (hl : l ∈ spectrum ℂ ((Acoup a c W).map (algebraMap ℝ ℂ))) :
    ∃ μ ∈ spectrum ℂ (W.map (algebraMap ℝ ℂ)), l = (c : ℂ) * μ + (a : ℂ) := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have h1 : (c : ℂ) * ((l - a) / c) + (a : ℂ) = l := by
    field_simp
    ring
  refine ⟨(l - a) / c, ?_, h1.symm⟩
  rw [map_Acoup, ← h1, spectrum.add_mem_add_iff] at hl
  exact (smul_mem_spec hc).mp hl

/-- Convexity of `c ↦ ‖cμ + a‖` in the form used: on `[c₁, c₂]` it is at most the larger
endpoint value. -/
lemma norm_le_max {a c c1 c2 : ℝ} (h1 : c1 ≤ c) (h2 : c ≤ c2) (hd : 0 < c2 - c1) (μ : ℂ) :
    ‖(c : ℂ) * μ + a‖ ≤ max ‖(c1 : ℂ) * μ + a‖ ‖(c2 : ℂ) * μ + a‖ := by
  have hp : 0 ≤ (c2 - c) / (c2 - c1) := div_nonneg (by linarith) hd.le
  have hq : 0 ≤ (c - c1) / (c2 - c1) := div_nonneg (by linarith) hd.le
  have hpq : (c2 - c) / (c2 - c1) + (c - c1) / (c2 - c1) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hd.ne']
    ring
  have hd' : (c2 : ℂ) - (c1 : ℂ) ≠ 0 := by
    have : ((c2 - c1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
    simpa using this
  have heq : (c : ℂ) * μ + a =
      (((c2 - c) / (c2 - c1) : ℝ) : ℂ) * ((c1 : ℂ) * μ + a) +
        (((c - c1) / (c2 - c1) : ℝ) : ℂ) * ((c2 : ℂ) * μ + a) := by
    push_cast
    field_simp
    ring
  set M := max ‖(c1 : ℂ) * μ + a‖ ‖(c2 : ℂ) * μ + a‖ with hM
  calc ‖(c : ℂ) * μ + a‖
      = ‖(((c2 - c) / (c2 - c1) : ℝ) : ℂ) * ((c1 : ℂ) * μ + a) +
          (((c - c1) / (c2 - c1) : ℝ) : ℂ) * ((c2 : ℂ) * μ + a)‖ := by rw [← heq]
    _ ≤ ‖(((c2 - c) / (c2 - c1) : ℝ) : ℂ) * ((c1 : ℂ) * μ + a)‖ +
          ‖(((c - c1) / (c2 - c1) : ℝ) : ℂ) * ((c2 : ℂ) * μ + a)‖ := norm_add_le _ _
    _ = (c2 - c) / (c2 - c1) * ‖(c1 : ℂ) * μ + a‖ +
          (c - c1) / (c2 - c1) * ‖(c2 : ℂ) * μ + a‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hp,
          Real.norm_of_nonneg hq]
    _ ≤ (c2 - c) / (c2 - c1) * M + (c - c1) / (c2 - c1) * M := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = M := by rw [← add_mul, hpq, one_mul]

/-- **The set `𝒞 = {c ≥ 0 : spr(aI + cW) < 1}` is an interval** (order-connected), for every
`a` and `W`; with `|a| < 1` it contains `0` (`sprB_range_contains`). -/
theorem C_ordConnected (a : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    Set.OrdConnected {c : ℝ | 0 ≤ c ∧ spr (Acoup a c W) < 1} := by
  refine ⟨fun c1 hc1 c2 hc2 c hc => ?_⟩
  obtain ⟨hcl, hcu⟩ := hc
  refine ⟨hc1.1.trans hcl, ?_⟩
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · unfold spr
    haveI : Subsingleton (Matrix (Fin n) (Fin n) ℂ) := inferInstance
    simp
  rcases eq_or_lt_of_le hcl with h | h
  · exact h ▸ hc1.2
  rcases eq_or_lt_of_le hcu with h' | h'
  · exact h' ▸ hc2.2
  have hc0 : c ≠ 0 := (hc1.1.trans_lt h).ne'
  have hd : 0 < c2 - c1 := by linarith
  refine lt_of_le_of_lt ?_ (max_lt hc1.2 hc2.2)
  show spectralRadius ℂ ((Acoup a c W).map (algebraMap ℝ ℂ)) ≤ _
  refine iSup₂_le fun l hl => ?_
  obtain ⟨μ, hμ, rfl⟩ := exists_of_mem_spec_Acoup a hc0 W hl
  have e1 : (‖(c1 : ℂ) * μ + a‖₊ : ENNReal) ≤ spr (Acoup a c1 W) :=
    le_iSup₂ (f := fun (k : ℂ) (_ : k ∈ spectrum ℂ ((Acoup a c1 W).map (algebraMap ℝ ℂ))) =>
      (‖k‖₊ : ENNReal)) _ (mem_spec_Acoup a c1 W hμ)
  have e2 : (‖(c2 : ℂ) * μ + a‖₊ : ENNReal) ≤ spr (Acoup a c2 W) :=
    le_iSup₂ (f := fun (k : ℂ) (_ : k ∈ spectrum ℂ ((Acoup a c2 W).map (algebraMap ℝ ℂ))) =>
      (‖k‖₊ : ENNReal)) _ (mem_spec_Acoup a c2 W hμ)
  have hreal := norm_le_max (a := a) h.le h'.le hd μ
  have hnn : ‖(c : ℂ) * μ + a‖₊ ≤ max ‖(c1 : ℂ) * μ + a‖₊ ‖(c2 : ℂ) * μ + a‖₊ := by
    rw [← NNReal.coe_le_coe, NNReal.coe_max]
    simpa using hreal
  calc (‖(c : ℂ) * μ + a‖₊ : ENNReal)
      ≤ ((max ‖(c1 : ℂ) * μ + a‖₊ ‖(c2 : ℂ) * μ + a‖₊ : NNReal) : ENNReal) :=
        ENNReal.coe_le_coe.mpr hnn
    _ = max (‖(c1 : ℂ) * μ + a‖₊ : ENNReal) (‖(c2 : ℂ) * μ + a‖₊ : ENNReal) :=
        ENNReal.coe_max _ _
    _ ≤ max (spr (Acoup a c1 W)) (spr (Acoup a c2 W)) := max_le_max e1 e2

/-- The paper's parenthetical claim in full: for `|a| < 1`, `𝒞` is an interval containing `0`. -/
theorem C_interval_containing_zero {a : ℝ} (ha : |a| < 1) (W : Matrix (Fin n) (Fin n) ℝ) :
    Set.OrdConnected {c : ℝ | 0 ≤ c ∧ spr (Acoup a c W) < 1} ∧
      (0 : ℝ) ∈ {c : ℝ | 0 ≤ c ∧ spr (Acoup a c W) < 1} := by
  refine ⟨C_ordConnected a W, le_rfl, ?_⟩
  obtain ⟨ε, hε, hspr⟩ := sprB_range_contains ha W
  exact hspr 0 le_rfl hε

end QAuditScaling.AuditInterval

#print axioms QAuditScaling.AuditInterval.C_ordConnected
#print axioms QAuditScaling.AuditInterval.C_interval_containing_zero
