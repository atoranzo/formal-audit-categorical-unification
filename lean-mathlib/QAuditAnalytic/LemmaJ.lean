import QAuditAnalytic.Core

/-!
# Lemma J (Gaussian integration and connectivity) and the min-cut sandwich

Paper statements (`C_categorical.tex`, `lem:J`; `D_weak_unification.tex`, `thm:cheeger`):

* **Lemma J.** `J(A,E) = min_π min_{B ∈ 𝔅_π} ½ log (det (E + (A-B) P (A-B)ᵀ) / det E)`, where
  `π` ranges over the bipartitions of the units, `P` is the stationary covariance
  (`P = A P Aᵀ + E`, `P ≻ 0`) and `𝔅_π` is the subspace of matrices with no coefficient crossing
  `π`.  For at least two units, `J > 0` iff the undirected graph of the off-diagonal support of
  `A` is connected.
* **Min-cut sandwich.** With `w_min = min_π ‖A_cross(π)‖_F²` and `κ_E = λ_max(E)/λ_min(E)`,
  `½ log (1 + w_min / κ_E) ≤ J ≤ ½ (λ_max(P)/λ_min(E)) w_min`.

Formal setting.  A bipartition `π = {S, Sᶜ}` is represented by one block `S : Finset (Fin n)`
with both blocks nonempty (`S` and `Sᶜ` represent the same `π`; every quantity is invariant
under `S ↦ Sᶜ`, because `Crosses S i j ↔ Crosses Sᶜ i j`).  The inner minimum is an infimum
(`sInf`) over `𝔅_π`; we prove that the set is nonempty and bounded below by `0`.  The outer
minimum is the infimum over the finite nonempty type of bipartitions, which is attained.
-/

open Matrix

namespace QAudit

variable {n : ℕ}

/-! ## Definitions -/

/-- `S` is one block of a bipartition `{S, Sᶜ}` of the units: both blocks are nonempty. -/
def IsBipartition (S : Finset (Fin n)) : Prop := S.Nonempty ∧ Sᶜ.Nonempty

/-- The bipartitions of the units `Fin n`, each represented by one of its two blocks. -/
abbrev Bipartition (n : ℕ) := {S : Finset (Fin n) // IsBipartition S}

/-- The coefficient `(i, j)` crosses the bipartition `{S, Sᶜ}`: exactly one of `i`, `j`
lies in `S`. -/
def Crosses (S : Finset (Fin n)) (i j : Fin n) : Prop := (i ∈ S ∧ j ∉ S) ∨ (i ∉ S ∧ j ∈ S)

instance (S : Finset (Fin n)) (i j : Fin n) : Decidable (Crosses S i j) := by
  unfold Crosses; infer_instance

/-- `𝔅_π`: the matrices with no coefficient crossing the bipartition. -/
def Bpi (S : Finset (Fin n)) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {B | ∀ i j, Crosses S i j → B i j = 0}

/-- `A_cross(π)`: keep only the coefficients of `A` that cross the bipartition. -/
def Across (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if Crosses S i j then A i j else 0

/-- `‖A_cross(π)‖_F²`, the squared Frobenius norm of the crossing coefficients. -/
def cutWeight (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i, ∑ j, Across A S i j ^ 2

/-- `w_min = min_π ‖A_cross(π)‖_F²` (a minimum over a finite nonempty set when `n ≥ 2`). -/
noncomputable def wmin (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨅ S : Bipartition n, cutWeight A S.1

/-- The objective `½ log (det (E + (A - B) P (A - B)ᵀ) / det E)`. -/
noncomputable def objective (E P A B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  1 / 2 * Real.log (det (E + (A - B) * P * (A - B)ᵀ) / det E)

/-- The inner infimum `inf_{B ∈ 𝔅_π} objective(B)` for a fixed bipartition. -/
noncomputable def Jcut (E P A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  sInf (objective E P A '' Bpi S)

/-- `J(A, E) = min_π inf_{B ∈ 𝔅_π} ½ log (det (E + (A-B) P (A-B)ᵀ) / det E)`, with the
covariance `P` given as data (the theorems assume `P ≻ 0` and, where the paper uses it,
`P = A P Aᵀ + E`). -/
noncomputable def J (E P A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨅ S : Bipartition n, Jcut E P A S.1

/-- The undirected graph of the off-diagonal support of `A`:
`i ~ j ↔ i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0)`. -/
def supportGraph (A : Matrix (Fin n) (Fin n) ℝ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => A i j ≠ 0 ∨ A j i ≠ 0

/-! ## Elementary facts -/

theorem supportGraph_adj {A : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} :
    (supportGraph A).Adj i j ↔ i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0) := by
  simp only [supportGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, h' | h'⟩
    · exact ⟨h, h'⟩
    · exact ⟨h, h'.symm⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, Or.inl h'⟩

theorem crosses_compl {S : Finset (Fin n)} {i j : Fin n} : Crosses Sᶜ i j ↔ Crosses S i j := by
  simp only [Crosses, Finset.mem_compl, not_not]
  tauto

/-- `S` and `Sᶜ` describe the same bipartition. -/
theorem isBipartition_compl {S : Finset (Fin n)} : IsBipartition Sᶜ ↔ IsBipartition S := by
  simp only [IsBipartition, compl_compl]
  exact And.comm

theorem Bpi_compl (S : Finset (Fin n)) : Bpi Sᶜ = Bpi S := by
  ext B
  simp only [Bpi, Set.mem_setOf_eq, crosses_compl]

theorem Across_compl (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    Across A Sᶜ = Across A S := by
  ext i j
  simp only [Across, of_apply, crosses_compl]

theorem crosses_ne {S : Finset (Fin n)} {i j : Fin n} (h : Crosses S i j) : i ≠ j := by
  rintro rfl
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> contradiction

theorem zero_mem_Bpi (S : Finset (Fin n)) : (0 : Matrix (Fin n) (Fin n) ℝ) ∈ Bpi S :=
  fun _ _ _ => rfl

theorem sub_Across_mem_Bpi (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    A - Across A S ∈ Bpi S := by
  intro i j h
  simp [Across, h]

theorem cutWeight_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    0 ≤ cutWeight A S :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- For `B ∈ 𝔅_π`, `‖A - B‖_F² ≥ ‖A_cross(π)‖_F²`. -/
theorem cutWeight_le_frob {A B : Matrix (Fin n) (Fin n) ℝ} {S : Finset (Fin n)}
    (hB : B ∈ Bpi S) : cutWeight A S ≤ ∑ i, ∑ j, (A - B) i j ^ 2 := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases h : Crosses S i j
  · simp [Across, h, hB i j h]
  · simp only [Across, of_apply, h, if_false]
    rw [sq (0 : ℝ), mul_zero]
    exact sq_nonneg _

/-- The two blocks `S`, `Sᶜ` of a bipartition give the same cut weight. -/
theorem cutWeight_compl (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    cutWeight A Sᶜ = cutWeight A S := by
  simp only [cutWeight, Across_compl]

theorem frob_Across (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    ∑ i, ∑ j, (A - (A - Across A S)) i j ^ 2 = cutWeight A S := by
  rw [sub_sub_cancel]
  rfl

theorem cutWeight_pos_iff {A : Matrix (Fin n) (Fin n) ℝ} {S : Finset (Fin n)} :
    0 < cutWeight A S ↔ ∃ i j, Crosses S i j ∧ A i j ≠ 0 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have : cutWeight A S = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases hc : Crosses S i j
      · simp [Across, hc, hne i j hc]
      · simp [Across, hc]
    linarith
  · rintro ⟨i, j, hc, hA⟩
    refine Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => sq_nonneg _)
        ⟨j, Finset.mem_univ _, ?_⟩⟩
    simp only [Across, of_apply, hc, if_true]
    positivity

theorem mem_Bpi_iff_cutWeight_eq_zero {A : Matrix (Fin n) (Fin n) ℝ} {S : Finset (Fin n)} :
    A ∈ Bpi S ↔ cutWeight A S = 0 := by
  constructor
  · intro h
    have := cutWeight_pos_iff (A := A) (S := S)
    have h2 : ¬ ∃ i j, Crosses S i j ∧ A i j ≠ 0 := by
      rintro ⟨i, j, hc, hA⟩
      exact hA (h i j hc)
    have h3 := cutWeight_nonneg A S
    by_contra hne
    exact h2 (this.mp (lt_of_le_of_ne h3 (Ne.symm hne)))
  · intro h i j hc
    by_contra hA
    have := cutWeight_pos_iff.mpr ⟨i, j, hc, hA⟩
    linarith

/-! ## The graph fact -/

/-- If the support graph is connected, every bipartition has a crossing coefficient. -/
theorem exists_cross_of_connected {A : Matrix (Fin n) (Fin n) ℝ}
    (hc : (supportGraph A).Connected) {S : Finset (Fin n)} (hS : IsBipartition S) :
    ∃ i j, Crosses S i j ∧ A i j ≠ 0 := by
  obtain ⟨a, ha⟩ := hS.1
  obtain ⟨b, hb⟩ := hS.2
  rw [Finset.mem_compl] at hb
  obtain ⟨p⟩ := hc.preconnected a b
  obtain ⟨d, -, hd1, hd2⟩ :=
    p.exists_boundary_dart (↑S : Set (Fin n)) (Finset.mem_coe.mpr ha)
      (fun h => hb (Finset.mem_coe.mp h))
  rw [Finset.mem_coe] at hd1 hd2
  have hadj := d.adj
  rw [supportGraph_adj] at hadj
  rcases hadj.2 with h | h
  · exact ⟨d.fst, d.snd, Or.inl ⟨hd1, hd2⟩, h⟩
  · exact ⟨d.snd, d.fst, Or.inr ⟨hd2, hd1⟩, h⟩

/-- If every bipartition has a crossing coefficient, the support graph is connected. -/
theorem connected_of_forall_cross [Nonempty (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ S : Finset (Fin n), IsBipartition S → ∃ i j, Crosses S i j ∧ A i j ≠ 0) :
    (supportGraph A).Connected := by
  classical
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (Fin n))
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨v₀, ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨w, hw⟩ := hne
  set S : Finset (Fin n) := Finset.univ.filter (fun v => (supportGraph A).Reachable v₀ v)
    with hSdef
  have hbip : IsBipartition S :=
    ⟨⟨v₀, by simp [S]⟩, ⟨w, by simp [S, hw]⟩⟩
  obtain ⟨i, j, hij, hA⟩ := h S hbip
  have hadj : (supportGraph A).Adj i j := supportGraph_adj.mpr ⟨crosses_ne hij, Or.inl hA⟩
  rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hj (hi.trans hadj.reachable)
  · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hi (hj.trans hadj.symm.reachable)

/-- The support graph is connected iff every bipartition has a crossing coefficient of `A`;
equivalently (`mem_Bpi_iff_cutWeight_eq_zero`), iff `A ∉ 𝔅_π` for every bipartition `π`. -/
theorem connected_iff_forall_cross [Nonempty (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ} :
    (supportGraph A).Connected ↔
      ∀ S : Finset (Fin n), IsBipartition S → ∃ i j, Crosses S i j ∧ A i j ≠ 0 :=
  ⟨fun hc _ hS => exists_cross_of_connected hc hS, connected_of_forall_cross⟩

#print axioms connected_iff_forall_cross

/-! ## Bipartitions form a finite nonempty type when `n ≥ 2` -/

theorem isBipartition_singleton_zero (hn : 2 ≤ n) :
    IsBipartition ({⟨0, by omega⟩} : Finset (Fin n)) :=
  ⟨Finset.singleton_nonempty _, ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩

theorem nonempty_bipartition (hn : 2 ≤ n) : Nonempty (Bipartition n) :=
  ⟨⟨_, isBipartition_singleton_zero hn⟩⟩

/-! ## Bounds on the objective -/

section objective

variable {E P A : Matrix (Fin n) (Fin n) ℝ}

theorem posSemidef_residual (hP : P.PosSemidef) (C : Matrix (Fin n) (Fin n) ℝ) :
    (C * P * Cᵀ).PosSemidef := by
  have := hP.mul_mul_conjTranspose_same C
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- `det (E + M) / det E ≥ 1 + tr (E⁻¹ M)` for the residual covariance `M`. -/
theorem one_add_trace_le_ratio (hE : E.PosDef) (hP : P.PosSemidef) (B : Matrix (Fin n) (Fin n) ℝ) :
    1 + trace (E⁻¹ * ((A - B) * P * (A - B)ᵀ)) ≤
      det (E + (A - B) * P * (A - B)ᵀ) / det E := by
  rw [le_div_iff₀ hE.det_pos, mul_comm]
  exact det_mul_one_add_trace_le hE (posSemidef_residual hP _)

theorem objective_nonneg (hE : E.PosDef) (hP : P.PosSemidef) (B : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ objective E P A B := by
  have h1 := one_add_trace_le_ratio (A := A) hE hP B
  have h2 := trace_inv_mul_nonneg hE (posSemidef_residual hP (A - B))
  unfold objective
  have : 0 ≤ Real.log (det (E + (A - B) * P * (A - B)ᵀ) / det E) :=
    Real.log_nonneg (by linarith)
  positivity

theorem objective_self (hE : E.PosDef) : objective E P A A = 0 := by
  simp [objective, div_self hE.det_pos.ne']

/-- Lower bound: `½ log (1 + (p₁/e₂) ‖A - B‖_F²) ≤ objective(B)` when `E ≤ e₂ • 1` and
`p₁ • 1 ≤ P` with `p₁ ≥ 0`. -/
theorem objective_ge (hE : E.PosDef) (hP : P.PosSemidef) {e₂ p₁ : ℝ} (he₂ : 0 < e₂)
    (hp₁ : 0 ≤ p₁) (hE₂ : (e₂ • 1 - E).PosSemidef) (hP₁ : (P - p₁ • 1).PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    1 / 2 * Real.log (1 + p₁ / e₂ * ∑ i, ∑ j, (A - B) i j ^ 2) ≤ objective E P A B := by
  have hM := posSemidef_residual hP (A - B)
  have h1 := one_add_trace_le_ratio (A := A) hE hP B
  have h2 := trace_le_mul_trace_inv_mul hE hM hE₂
  have h3 := trace_mul_mul_transpose_ge hP₁ (A - B)
  have hF : 0 ≤ ∑ i, ∑ j, (A - B) i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4 : p₁ / e₂ * ∑ i, ∑ j, (A - B) i j ^ 2 ≤ trace (E⁻¹ * ((A - B) * P * (A - B)ᵀ)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ he₂]
    linarith
  have hpos : 0 < 1 + p₁ / e₂ * ∑ i, ∑ j, (A - B) i j ^ 2 := by positivity
  have := Real.log_le_log hpos (le_trans (by linarith) h1)
  unfold objective
  linarith

/-- Upper bound: `objective(B) ≤ ½ (p₂/e₁) ‖A - B‖_F²` when `e₁ • 1 ≤ E` (`e₁ > 0`) and
`P ≤ p₂ • 1`. -/
theorem objective_le (hE : E.PosDef) (hP : P.PosSemidef) {e₁ p₂ : ℝ} (he₁ : 0 < e₁)
    (hE₁ : (E - e₁ • 1).PosSemidef) (hP₂ : (p₂ • 1 - P).PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    objective E P A B ≤ 1 / 2 * (p₂ / e₁ * ∑ i, ∑ j, (A - B) i j ^ 2) := by
  have hM := posSemidef_residual hP (A - B)
  have h1 := log_det_add_sub_le hE hM
  have h2 := mul_trace_inv_mul_le_trace hE hM hE₁
  have h3 := trace_mul_mul_transpose_le hP₂ (A - B)
  have hdet : 0 < det (E + (A - B) * P * (A - B)ᵀ) := det_add_pos hE hM
  have h4 : trace (E⁻¹ * ((A - B) * P * (A - B)ᵀ)) ≤ p₂ / e₁ * ∑ i, ∑ j, (A - B) i j ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ he₁]
    linarith
  unfold objective
  rw [Real.log_div hdet.ne' hE.det_pos.ne']
  linarith

end objective

/-! ## The inner infimum -/

section Jcut

variable {E P A : Matrix (Fin n) (Fin n) ℝ}

/-- The set over which the inner infimum is taken is nonempty. -/
theorem objective_image_nonempty (S : Finset (Fin n)) : (objective E P A '' Bpi S).Nonempty :=
  ⟨_, Set.mem_image_of_mem _ (zero_mem_Bpi S)⟩

/-- The set over which the inner infimum is taken is bounded below by `0`. -/
theorem objective_image_bddBelow (hE : E.PosDef) (hP : P.PosSemidef) (S : Finset (Fin n)) :
    BddBelow (objective E P A '' Bpi S) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨B, -, rfl⟩
  exact objective_nonneg hE hP B

theorem Jcut_le (hE : E.PosDef) (hP : P.PosSemidef) {S : Finset (Fin n)}
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B ∈ Bpi S) : Jcut E P A S ≤ objective E P A B :=
  csInf_le (objective_image_bddBelow hE hP S) (Set.mem_image_of_mem _ hB)

theorem le_Jcut {S : Finset (Fin n)} {c : ℝ} (h : ∀ B ∈ Bpi S, c ≤ objective E P A B) :
    c ≤ Jcut E P A S := by
  refine le_csInf (objective_image_nonempty S) ?_
  rintro _ ⟨B, hB, rfl⟩
  exact h B hB

theorem Jcut_nonneg (hE : E.PosDef) (hP : P.PosSemidef) (S : Finset (Fin n)) :
    0 ≤ Jcut E P A S :=
  le_Jcut fun B _ => objective_nonneg hE hP B

/-- The two blocks `S`, `Sᶜ` of a bipartition give the same inner infimum. -/
theorem Jcut_compl (S : Finset (Fin n)) : Jcut E P A Sᶜ = Jcut E P A S := by
  simp only [Jcut, Bpi_compl]

end Jcut

/-! ## The outer minimum over bipartitions -/

section Jmin

variable {E P A : Matrix (Fin n) (Fin n) ℝ}

theorem J_le_Jcut (S : Bipartition n) : J E P A ≤ Jcut E P A S.1 :=
  ciInf_le (Set.finite_range _).bddBelow S

theorem le_J (hn : 2 ≤ n) {c : ℝ} (h : ∀ S : Bipartition n, c ≤ Jcut E P A S.1) :
    c ≤ J E P A :=
  haveI := nonempty_bipartition hn
  le_ciInf h

/-- The outer minimum is attained. -/
theorem exists_J_eq_Jcut (hn : 2 ≤ n) : ∃ S : Bipartition n, Jcut E P A S.1 = J E P A :=
  haveI := nonempty_bipartition hn
  exists_eq_ciInf_of_finite

theorem wmin_le (A : Matrix (Fin n) (Fin n) ℝ) (S : Bipartition n) : wmin A ≤ cutWeight A S.1 :=
  ciInf_le (Set.finite_range _).bddBelow S

/-- `w_min` is attained by some bipartition. -/
theorem exists_wmin_eq (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ S : Bipartition n, cutWeight A S.1 = wmin A :=
  haveI := nonempty_bipartition hn
  exists_eq_ciInf_of_finite

theorem wmin_nonneg (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ wmin A := by
  obtain ⟨S, hS⟩ := exists_wmin_eq hn A
  rw [← hS]
  exact cutWeight_nonneg A S.1

theorem J_nonneg (hn : 2 ≤ n) (hE : E.PosDef) (hP : P.PosSemidef) : 0 ≤ J E P A :=
  le_J hn fun S => Jcut_nonneg hE hP S.1

end Jmin

/-! ## Lemma J -/

section lemmaJ

variable {E P A : Matrix (Fin n) (Fin n) ℝ}

/-- If some coefficient of `A` crosses the bipartition, the inner infimum is positive. -/
theorem Jcut_pos (hn : 2 ≤ n) (hE : E.PosDef) (hP : P.PosDef) {S : Finset (Fin n)}
    (hcross : ∃ i j, Crosses S i j ∧ A i j ≠ 0) : 0 < Jcut E P A S := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hw : 0 < cutWeight A S := cutWeight_pos_iff.mpr hcross
  -- Loewner bounds `λ_min(P) • 1 ≤ P` and `E ≤ λ_max(E) • 1`
  have hp₁ : 0 < lamMin hP.1 := lamMin_pos hP
  have he₂ : 0 < lamMax hE.1 := by
    obtain ⟨i, -⟩ := exists_eigenvalue_eq_lamMax hE.1
    exact lt_of_lt_of_le (hE.eigenvalues_pos i) (le_lamMax hE.1 i)
  set c : ℝ := 1 / 2 * Real.log (1 + lamMin hP.1 / lamMax hE.1 * cutWeight A S) with hc
  have hcpos : 0 < c := by
    have : 0 < lamMin hP.1 / lamMax hE.1 * cutWeight A S := by positivity
    have := Real.log_pos (by linarith : 1 < 1 + lamMin hP.1 / lamMax hE.1 * cutWeight A S)
    rw [hc]; positivity
  refine lt_of_lt_of_le hcpos (le_Jcut fun B hB => ?_)
  refine le_trans ?_ (objective_ge hE hP.posSemidef he₂ hp₁.le (posSemidef_lamMax_sub hE.1)
    (posSemidef_sub_lamMin hP.1) B)
  have hle := cutWeight_le_frob (A := A) hB
  have h0 : 0 < 1 + lamMin hP.1 / lamMax hE.1 * cutWeight A S := by positivity
  have := Real.log_le_log h0 (show 1 + lamMin hP.1 / lamMax hE.1 * cutWeight A S ≤
    1 + lamMin hP.1 / lamMax hE.1 * ∑ i, ∑ j, (A - B) i j ^ 2 by gcongr)
  rw [hc]; linarith

/-- If `A ∈ 𝔅_π` (no coefficient of `A` crosses `π`), the inner infimum is `0`, attained at
`B = A`. -/
theorem Jcut_eq_zero (hE : E.PosDef) (hP : P.PosSemidef) {S : Finset (Fin n)}
    (hA : A ∈ Bpi S) : Jcut E P A S = 0 :=
  le_antisymm ((Jcut_le hE hP hA).trans_eq (objective_self hE)) (Jcut_nonneg hE hP S)

/-- **Lemma J** (`lem:J`), with the covariance `P` only required to be positive definite:
for at least two units, `J > 0` iff the undirected graph of the off-diagonal support of `A`
is connected. -/
theorem lemmaJ (hn : 2 ≤ n) (hE : E.PosDef) (hP : P.PosDef) :
    0 < J E P A ↔ (supportGraph A).Connected := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  constructor
  · intro hJ
    rw [connected_iff_forall_cross]
    intro S hS
    by_contra hne
    have hA : A ∈ Bpi S := by
      intro i j hc
      by_contra hA
      exact hne ⟨i, j, hc, hA⟩
    have h1 := J_le_Jcut (E := E) (P := P) (A := A) ⟨S, hS⟩
    rw [Jcut_eq_zero hE hP.posSemidef hA] at h1
    linarith
  · intro hc
    obtain ⟨S, hS⟩ := exists_J_eq_Jcut (E := E) (P := P) (A := A) hn
    rw [← hS]
    exact Jcut_pos hn hE hP (exists_cross_of_connected hc S.2)

#print axioms lemmaJ

/-- `J = 0` exactly on disconnected supports (for at least two units). -/
theorem J_eq_zero_iff (hn : 2 ≤ n) (hE : E.PosDef) (hP : P.PosDef) :
    J E P A = 0 ↔ ¬ (supportGraph A).Connected := by
  rw [← lemmaJ hn hE hP]
  have := J_nonneg (E := E) (P := P) (A := A) hn hE hP.posSemidef
  constructor
  · intro h; rw [h]; exact lt_irrefl 0
  · intro h; push_neg at h; linarith

#print axioms J_eq_zero_iff

/-- The stationary covariance dominates the noise: `P = A P Aᵀ + E` and `P ⪰ 0` give
`E ≤ P` in the Loewner order. -/
theorem posSemidef_P_sub_E (hP : P.PosSemidef) (hstat : P = A * P * Aᵀ + E) :
    (P - E).PosSemidef := by
  have h : P - E = A * P * Aᵀ := by
    conv_lhs => rw [hstat]
    rw [add_sub_cancel_right]
  rw [h]
  exact posSemidef_residual hP A

/-- **Lemma J** with the paper's hypotheses: `E ≻ 0`, and `P` a positive definite solution of
the stationarity equation `P = A P Aᵀ + E` (the stationarity equation is not needed for this
statement). -/
theorem lemmaJ_stationary (hn : 2 ≤ n) (hE : E.PosDef) (hP : P.PosDef)
    (_hstat : P = A * P * Aᵀ + E) :
    0 < J E P A ↔ (supportGraph A).Connected :=
  lemmaJ hn hE hP

#print axioms lemmaJ_stationary

end lemmaJ

/-! ## The min-cut sandwich -/

section sandwich

variable {E P A : Matrix (Fin n) (Fin n) ℝ}

theorem le_of_loewner_bounds (hn : 2 ≤ n) {X : Matrix (Fin n) (Fin n) ℝ} {a b : ℝ}
    (ha : (X - a • 1).PosSemidef) (hb : (b • 1 - X).PosSemidef) : a ≤ b := by
  have h := (hb.add ha).trace_nonneg
  rw [sub_add_sub_cancel, ← sub_smul, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  nlinarith

/-- **Min-cut sandwich, lower bound** (`thm:cheeger`), with arbitrary Loewner bounds
`e₁ • 1 ≤ E ≤ e₂ • 1` (`e₁ > 0`) in place of `λ_min(E)`, `λ_max(E)`; `κ = e₂ / e₁`. -/
theorem sandwich_lower (hn : 2 ≤ n) (hE : E.PosDef) (hP : P.PosDef)
    (hstat : P = A * P * Aᵀ + E) {e₁ e₂ : ℝ} (he₁ : 0 < e₁)
    (hE₁ : (E - e₁ • 1).PosSemidef) (hE₂ : (e₂ • 1 - E).PosSemidef) :
    1 / 2 * Real.log (1 + wmin A / (e₂ / e₁)) ≤ J E P A := by
  have he₂ : 0 < e₂ := lt_of_lt_of_le he₁ (le_of_loewner_bounds hn hE₁ hE₂)
  -- `e₁ • 1 ≤ E ≤ P`
  have hP₁ : (P - e₁ • 1).PosSemidef := by
    have := (posSemidef_P_sub_E hP.posSemidef hstat).add hE₁
    rwa [sub_add_sub_cancel] at this
  have hw := wmin_nonneg hn A
  have hrw : wmin A / (e₂ / e₁) = e₁ / e₂ * wmin A := by
    field_simp
  rw [hrw]
  refine le_J hn fun S => le_Jcut fun B hB => ?_
  refine le_trans ?_ (objective_ge hE hP.posSemidef he₂ he₁.le hE₂ hP₁ B)
  have h1 : wmin A ≤ ∑ i, ∑ j, (A - B) i j ^ 2 :=
    (wmin_le A S).trans (cutWeight_le_frob hB)
  have h0 : 0 < 1 + e₁ / e₂ * wmin A := by positivity
  have := Real.log_le_log h0 (show 1 + e₁ / e₂ * wmin A ≤
    1 + e₁ / e₂ * ∑ i, ∑ j, (A - B) i j ^ 2 by gcongr)
  linarith

#print axioms sandwich_lower

/-- **Min-cut sandwich, upper bound** (`thm:cheeger`), with arbitrary Loewner bounds
`e₁ • 1 ≤ E` (`e₁ > 0`) and `P ≤ p₂ • 1` in place of `λ_min(E)`, `λ_max(P)`.  Only `P ⪰ 0`
is used. -/
theorem sandwich_upper (hn : 2 ≤ n) (hE : E.PosDef) (hP : P.PosSemidef) {e₁ p₂ : ℝ}
    (he₁ : 0 < e₁) (hE₁ : (E - e₁ • 1).PosSemidef) (hP₂ : (p₂ • 1 - P).PosSemidef) :
    J E P A ≤ 1 / 2 * (p₂ / e₁) * wmin A := by
  obtain ⟨S, hS⟩ := exists_wmin_eq hn A
  have h1 := J_le_Jcut (E := E) (P := P) (A := A) S
  have h2 := Jcut_le (A := A) hE hP (sub_Across_mem_Bpi A S.1)
  have h3 := objective_le (A := A) hE hP he₁ hE₁ hP₂ (A - Across A S.1)
  rw [frob_Across, hS] at h3
  linarith

#print axioms sandwich_upper

/-- **Min-cut sandwich** (`thm:cheeger`) exactly as in the paper, with
`κ_E = λ_max(E) / λ_min(E)` and the constant `λ_max(P) / λ_min(E)`:
`½ log (1 + w_min / κ_E) ≤ J ≤ ½ (λ_max(P) / λ_min(E)) w_min`. -/
theorem sandwich (hn : 2 ≤ n) (hE : E.PosDef) (hP : P.PosDef)
    (hstat : P = A * P * Aᵀ + E) :
    1 / 2 * Real.log (1 + wmin A / (lamMax hE.1 / lamMin hE.1)) ≤ J E P A ∧
      J E P A ≤ 1 / 2 * (lamMax hP.1 / lamMin hE.1) * wmin A := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact ⟨sandwich_lower hn hE hP hstat (lamMin_pos hE) (posSemidef_sub_lamMin hE.1)
      (posSemidef_lamMax_sub hE.1),
    sandwich_upper hn hE hP.posSemidef (lamMin_pos hE) (posSemidef_sub_lamMin hE.1)
      (posSemidef_lamMax_sub hP.1)⟩

#print axioms sandwich

end sandwich

/-! ## Attainment of the inner minimum (optional target) -/

section attain

open Filter Topology

variable {E P A : Matrix (Fin n) (Fin n) ℝ}

/-- The objective is continuous in `B`. -/
theorem continuous_objective (hE : E.PosDef) (hP : P.PosSemidef) :
    Continuous (objective E P A) := by
  unfold objective
  refine continuous_const.mul (Continuous.log ?_ ?_)
  · refine Continuous.div_const ?_ _
    refine Continuous.matrix_det ?_
    refine continuous_const.add ?_
    have hc : Continuous fun B : Matrix (Fin n) (Fin n) ℝ => A - B :=
      continuous_const.sub continuous_id
    exact (hc.matrix_mul continuous_const).matrix_mul hc.matrix_transpose
  · intro B
    exact (div_pos (det_add_pos hE (posSemidef_residual hP _)) hE.det_pos).ne'

/-- `𝔅_π` is closed. -/
theorem isClosed_Bpi (S : Finset (Fin n)) : IsClosed (Bpi S) := by
  have : Bpi S = ⋂ i, ⋂ j, {B : Matrix (Fin n) (Fin n) ℝ | Crosses S i j → B i j = 0} := by
    ext B; simp [Bpi]
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases h : Crosses S i j
  · simp only [h, true_implies]
    exact isClosed_eq (continuous_id.matrix_elem i j) continuous_const
  · simp [h]

/-- **Attainment of the inner minimum** (paper: "it is attained, because the objective is
coercive in `B`"): for every bipartition the infimum over `𝔅_π` is a minimum. -/
theorem exists_minimizer (hn : 0 < n) (hE : E.PosDef) (hP : P.PosDef) (S : Finset (Fin n)) :
    ∃ B ∈ Bpi S, objective E P A B = Jcut E P A S := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hp₁ : 0 < lamMin hP.1 := lamMin_pos hP
  have he₂ : 0 < lamMax hE.1 := by
    obtain ⟨i, -⟩ := exists_eigenvalue_eq_lamMax hE.1
    exact lt_of_lt_of_le (hE.eigenvalues_pos i) (le_lamMax hE.1 i)
  set c : ℝ := lamMin hP.1 / lamMax hE.1 with hc
  have hcpos : 0 < c := div_pos hp₁ he₂
  have hcoer : ∀ B, 1 / 2 * Real.log (1 + c * ∑ i, ∑ j, (A - B) i j ^ 2) ≤
      objective E P A B := fun B =>
    objective_ge hE hP.posSemidef he₂ hp₁.le (posSemidef_lamMax_sub hE.1)
      (posSemidef_sub_lamMin hP.1) B
  set f0 : ℝ := objective E P A 0 with hf0
  set R : ℝ := Real.exp (2 * f0) / c with hR
  have hR0 : 0 ≤ R := by positivity
  set r : ℝ := Real.sqrt R with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg R
  have hrR : r ^ 2 = R := Real.sq_sqrt hR0
  set K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    Set.pi Set.univ fun i => Set.pi Set.univ fun j => Set.Icc (A i j - r) (A i j + r) with hK
  have hKc : IsCompact K := isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc
  have hfar : ∀ B ∈ Kᶜ, f0 ≤ objective E P A B := by
    intro B hBK
    have hall : ¬ ∀ i j, A i j - r ≤ B i j ∧ B i j ≤ A i j + r := by
      intro hall
      exact hBK (fun i _ j _ => hall i j)
    push_neg at hall
    obtain ⟨i, j, hij⟩ := hall
    have hfar : R ≤ (A - B) i j ^ 2 := by
      rw [sub_apply, ← hrR]
      by_cases h1 : A i j - r ≤ B i j
      · have h2 := hij h1
        nlinarith
      · push_neg at h1
        nlinarith
    have h1 : (A - B) i j ^ 2 ≤ ∑ j', (A - B) i j' ^ 2 :=
      Finset.single_le_sum (f := fun j' => (A - B) i j' ^ 2) (fun j' _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h2 : ∑ j', (A - B) i j' ^ 2 ≤ ∑ i', ∑ j', (A - B) i' j' ^ 2 :=
      Finset.single_le_sum (f := fun i' => ∑ j', (A - B) i' j' ^ 2)
        (fun i' _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hcR : c * R = Real.exp (2 * f0) := by
      rw [hR]; field_simp
    have h3 : 2 * f0 ≤ Real.log (1 + c * R) := by
      rw [hcR]
      calc 2 * f0 = Real.log (Real.exp (2 * f0)) := (Real.log_exp _).symm
        _ ≤ Real.log (1 + Real.exp (2 * f0)) :=
          Real.log_le_log (Real.exp_pos _) (by linarith)
    have h4 : Real.log (1 + c * R) ≤ Real.log (1 + c * ∑ i', ∑ j', (A - B) i' j' ^ 2) :=
      Real.log_le_log (by positivity) (by gcongr; linarith)
    have := hcoer B
    linarith
  obtain ⟨B, hB, hmin⟩ :=
    (continuous_objective (A := A) hE hP.posSemidef).continuousOn.exists_isMinOn'
    (isClosed_Bpi S) (zero_mem_Bpi S) (by
      rw [(hasBasis_cocompact.inf_principal _).eventually_iff]
      exact ⟨K, hKc, fun B hB => hfar B hB.1⟩)
  refine ⟨B, hB, ?_⟩
  refine (IsLeast.csInf_eq ⟨Set.mem_image_of_mem _ hB, ?_⟩).symm
  rintro _ ⟨B', hB', rfl⟩
  exact isMinOn_iff.mp hmin B' hB'

/-- Both minima in the definition of `J` are attained: there are a bipartition `π` and a
`B ∈ 𝔅_π` with `J = ½ log (det (E + (A-B) P (A-B)ᵀ) / det E)`. -/
theorem exists_J_minimizer (hn : 2 ≤ n) (hE : E.PosDef) (hP : P.PosDef) :
    ∃ S : Bipartition n, ∃ B ∈ Bpi S.1, objective E P A B = J E P A := by
  obtain ⟨S, hS⟩ := exists_J_eq_Jcut (E := E) (P := P) (A := A) hn
  obtain ⟨B, hB, hBeq⟩ := exists_minimizer (A := A) (by omega) hE hP S.1
  exact ⟨S, B, hB, hBeq.trans hS⟩

end attain

#print axioms exists_minimizer
#print axioms exists_J_minimizer

/-! ## Sanity checks: the hypotheses are satisfiable and both cases of Lemma J occur -/

namespace LemmaJExample

/-- The coupling matrix of a two-unit system with a single coupling `A₀₁ = 1/2`. -/
noncomputable def Aex : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 / 2 else 0

/-- Its stationary covariance for `E = 1`: `P = diag (5/4, 1)`. -/
noncomputable def Pex : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![5 / 4, 1]

theorem Pex_posDef : Pex.PosDef := by
  rw [Pex, posDef_diagonal_iff]
  intro i; fin_cases i <;> norm_num

theorem Pex_stationary : Pex = Aex * Pex * Aexᵀ + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Aex, Pex, Matrix.mul_apply, Matrix.transpose_apply, diagonal]

theorem Aex_connected : (supportGraph Aex).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun w => ?_⟩
  fin_cases w
  · exact SimpleGraph.Reachable.refl _
  · refine SimpleGraph.Adj.reachable (supportGraph_adj.mpr ⟨by decide, Or.inl ?_⟩)
    simp [Aex]

/-- Sanity check (non-vacuity): the hypotheses of `lemmaJ_stationary` hold for a concrete
system, and `J > 0` there. -/
example : 0 < J 1 Pex Aex :=
  (lemmaJ_stationary (le_refl 2) PosDef.one Pex_posDef Pex_stationary).mpr Aex_connected

/-- Sanity check: a decoupled system (`A = 0`, `E = P = 1`) has `J = 0`. -/
example : J (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rw [J_eq_zero_iff (le_refl 2) PosDef.one PosDef.one]
  intro hc
  obtain ⟨i, j, -, h⟩ := exists_cross_of_connected hc (isBipartition_singleton_zero (le_refl 2))
  exact h rfl

theorem crosses_zero_one {S : Finset (Fin 2)} (hS : IsBipartition S) : Crosses S 0 1 := by
  obtain ⟨a, ha⟩ := hS.1
  obtain ⟨b, hb⟩ := hS.2
  rw [Finset.mem_compl] at hb
  fin_cases a <;> fin_cases b
  · exact absurd ha hb
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨hb, ha⟩
  · exact absurd ha hb

theorem cutWeight_Aex {S : Finset (Fin 2)} (hS : IsBipartition S) : cutWeight Aex S = 1 / 4 := by
  have h01 := crosses_zero_one hS
  simp [cutWeight, Across, Fin.sum_univ_two, Aex, h01]
  norm_num

theorem wmin_Aex : wmin Aex = 1 / 4 := by
  haveI := nonempty_bipartition (le_refl 2)
  have : (fun S : Bipartition 2 => cutWeight Aex S.1) = fun _ => 1 / 4 :=
    funext fun S => cutWeight_Aex S.2
  rw [wmin, this, ciInf_const]

/-- Sanity check (non-vacuity of the sandwich): the Loewner-bound hypotheses hold on the
concrete system (`e₁ = e₂ = 1` for `E = 1`, `p₂ = 5/4` for `P = diag (5/4, 1)`), and since
`w_min = 1/4` the sandwich gives `½ log (5/4) ≤ J ≤ 5/32`. -/
example : 1 / 2 * Real.log (5 / 4) ≤ J 1 Pex Aex ∧ J 1 Pex Aex ≤ 5 / 32 := by
  have h1 : ((1 : Matrix (Fin 2) (Fin 2) ℝ) - (1 : ℝ) • 1).PosSemidef := by
    rw [one_smul, sub_self]; exact PosSemidef.zero
  have h2 : ((1 : ℝ) • 1 - (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef := by
    rw [one_smul, sub_self]; exact PosSemidef.zero
  have h3 : ((5/4 : ℝ) • 1 - Pex).PosSemidef := by
    have : (5/4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - Pex = diagonal ![0, 1/4] := by
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [Pex, diagonal]
    rw [this]
    exact PosSemidef.diagonal (fun i => by fin_cases i <;> norm_num)
  have hl := sandwich_lower (le_refl 2) PosDef.one Pex_posDef Pex_stationary one_pos h1 h2
  have hu := sandwich_upper (A := Aex) (le_refl 2) PosDef.one Pex_posDef.posSemidef one_pos h1 h3
  rw [wmin_Aex] at hl hu
  constructor
  · convert hl using 3; norm_num
  · convert hu using 1; norm_num

end LemmaJExample

end QAudit
