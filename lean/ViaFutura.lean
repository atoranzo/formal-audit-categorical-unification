/-!
# ViaFutura.lean — which reformulation of S_u escapes the connected-transversality
# collapse. Lean 4 core (4.24.0), no Mathlib.

* `exact_covariance_gives_Su`: exact covariance along perturbation steps
  (Δu = ΔH(Φ)) implies equal u at the two ends of any chain with equal Φ; applied to
  the symmetric closure of the steps (`exact_covariance_components`), S_u holds on
  every connected component of the step graph: no escape. Values in Int.
* `order_all_pairs_collapse`: the order clause B over all pairs, with a transversal κ
  of product image (two Φ-levels, two κ-classes), forces u constant: no escape.
  `order_all_pairs_general` is the general form: if each of two classes occurs below
  the other across a strict Φ-gap, their values coincide.
* `intervention_monotonicity_escapes`: monotonicity restricted to a declared class of
  intervention pairs is satisfiable with u non-constant, u factoring through a
  transversal κ of product image, and S_u false: it escapes the collapse (at the
  price of comparing only intervention-related pairs).
* `equality_on_fibre_steps_collapses`: if the intervention class also contains
  Φ-preserving steps on which equality is required, and they chain together the
  realizations of a fibre, S_u returns on that fibre: the exact frontier.
-/

namespace ViaFutura

attribute [local instance] Classical.propDecidable

/-- Reflexive–transitive closure of a step relation (no Mathlib). -/
inductive Chain {D : Type} (T : D → D → Prop) : D → D → Prop
  | refl (a : D) : Chain T a a
  | step {a b c : D} : Chain T a b → T b c → Chain T a c

/-- Exact covariance: along every step, u changes exactly as H ∘ Φ. Then u − H ∘ Φ is
constant on chains, so equal Φ at the two ends of a chain forces equal u. -/
theorem exact_covariance_gives_Su {D V : Type} (T : D → D → Prop) (Φ : D → V)
    (u : D → Int) (H : V → Int)
    (hstep : ∀ s t, T s t → u t - u s = H (Φ t) - H (Φ s)) :
    ∀ s t, Chain T s t → Φ s = Φ t → u s = u t := by
  intro s t hc
  have key : u t - H (Φ t) = u s - H (Φ s) := by
    induction hc with
    | refl => rfl
    | @step b c _ hT ih =>
      have := hstep b c hT
      omega
  intro hΦ
  rw [hΦ] at key
  omega

/-- Symmetric closure of a step relation. -/
def Sym {D : Type} (T : D → D → Prop) : D → D → Prop := fun s t => T s t ∨ T t s

/-- Exact covariance is symmetric, so it also holds along the symmetric closure: S_u on
every connected component of the (undirected) step graph. -/
theorem exact_covariance_components {D V : Type} (T : D → D → Prop) (Φ : D → V)
    (u : D → Int) (H : V → Int)
    (hstep : ∀ s t, T s t → u t - u s = H (Φ t) - H (Φ s)) :
    ∀ s t, Chain (Sym T) s t → Φ s = Φ t → u s = u t := by
  apply exact_covariance_gives_Su (Sym T) Φ u H
  intro s t h
  rcases h with h | h
  · exact hstep s t h
  · have := hstep t s h
    omega

/-! Product-image model: Φ ∈ {0,1}, κ ∈ {0,1}, all four combinations realised. -/
def Φp : Fin 4 → Nat := fun s => s.val / 2
def κp : Fin 4 → Nat := fun s => s.val % 2

/-- The order clause B over ALL pairs (Φ s < Φ t ⇒ u s ≤ u t), with u = f ∘ κ and a
product image, forces f 0 = f 1, hence u constant. -/
theorem order_all_pairs_collapse (f : Nat → Int)
    (hB : ∀ s t : Fin 4, Φp s < Φp t → f (κp s) ≤ f (κp t)) : f 0 = f 1 := by
  have h1 := hB 0 3 (by decide)   -- κ 0 at level 0, κ 1 at level 1
  have h2 := hB 1 2 (by decide)   -- κ 1 at level 0, κ 0 at level 1
  have e0 : κp 0 = 0 := by decide
  have e1 : κp 1 = 1 := by decide
  have e2 : κp 2 = 0 := by decide
  have e3 : κp 3 = 1 := by decide
  rw [e0, e3] at h1
  rw [e1, e2] at h2
  omega

/-- General form: B over all pairs with u = f ∘ κ; if class k occurs strictly below
class k' and k' occurs strictly below k, then f k = f k'. -/
theorem order_all_pairs_general {D V K : Type} [LT V] (Φ : D → V) (κ : D → K)
    (f : K → Int) (hB : ∀ s t, Φ s < Φ t → f (κ s) ≤ f (κ t)) (k k' : K)
    (s t s' t' : D) (h1 : Φ s < Φ t) (h2 : Φ s' < Φ t')
    (hs : κ s = k) (ht : κ t = k') (hs' : κ s' = k') (ht' : κ t' = k) : f k = f k' := by
  have a := hB s t h1
  have b := hB s' t' h2
  rw [hs, ht] at a
  rw [hs', ht'] at b
  exact Int.le_antisymm a b

/-- Interventions available in the model: three level-raising steps. -/
def Tint : Fin 4 → Fin 4 → Prop := fun s t => (s.val = 0 ∧ t.val = 2) ∨ (s.val = 0 ∧ t.val = 3) ∨ (s.val = 1 ∧ t.val = 3)

/-- Monotonicity restricted to intervention pairs holds for u = κ (non-constant,
transversal, product image) while S_u fails. -/
theorem intervention_monotonicity_escapes :
    (∀ s t : Fin 4, Tint s t → Φp s < Φp t → κp s ≤ κp t) ∧
    κp 0 ≠ κp 1 ∧ Φp 0 = Φp 1 := by
  refine ⟨?_, by decide, by decide⟩
  intro s t h _
  rcases h with ⟨hs, ht⟩ | ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> simp [κp, hs, ht]

/-- Frontier: if equality is required on Φ-preserving steps and such steps chain two
realizations, they get equal u (S_u on that fibre). -/
theorem equality_on_fibre_steps_collapses {D V U : Type} (T : D → D → Prop) (Φ : D → V)
    (u : D → U) (heq : ∀ s t, T s t → Φ s = Φ t → u s = u t)
    (hpres : ∀ s t, T s t → Φ s = Φ t) :
    ∀ s t, Chain T s t → u s = u t := by
  intro s t hc
  induction hc with
  | refl => rfl
  | @step b c _ hT ih =>
    exact ih.trans (heq b c hT (hpres b c hT))


/-! ## Exact frontier of the escape: the intervention digraph on κ-classes -/

/-- Edge k → k' when some Φ-raising intervention takes a κ = k realization to a κ = k' one. -/
def Edge {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V) (κ : D → K) (k k' : K) : Prop :=
  ∃ s t, T s t ∧ Φ s < Φ t ∧ κ s = k ∧ κ t = k'

/-- With u = f ∘ κ, intervention monotonicity is exactly monotonicity of f along the
edges of the intervention digraph. -/
theorem im_iff_edges {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V) (κ : D → K)
    (f : K → Int) :
    (∀ s t, T s t → Φ s < Φ t → f (κ s) ≤ f (κ t)) ↔
      (∀ k k', Edge T Φ κ k k' → f k ≤ f k') := by
  constructor
  · intro h k k' ⟨s, t, hT, hlt, hs, ht⟩
    rw [← hs, ← ht]; exact h s t hT hlt
  · intro h s t hT hlt
    exact h _ _ ⟨s, t, hT, hlt, rfl, rfl⟩

/-- Monotone along paths of the digraph; hence f is constant on strongly connected
components (mutually reachable classes get equal values). -/
theorem monotone_on_reach {K : Type} (E : K → K → Prop) (f : K → Int)
    (h : ∀ k k', E k k' → f k ≤ f k') : ∀ k k', Chain E k k' → f k ≤ f k' := by
  intro k k' hc
  induction hc with
  | refl => exact Int.le_refl _
  | @step b c _ hE ih => exact Int.le_trans ih (h b c hE)

theorem constant_on_scc {K : Type} (E : K → K → Prop) (f : K → Int)
    (h : ∀ k k', E k k' → f k ≤ f k') (k k' : K)
    (h1 : Chain E k k') (h2 : Chain E k' k) : f k = f k' :=
  Int.le_antisymm (monotone_on_reach E f h k k' h1) (monotone_on_reach E f h k' k h2)

/-- If k is not reachable from k' (as happens for some pair whenever the digraph is
not strongly connected), a monotone f with f k ≠ f k' exists: the indicator of the
classes reachable from k'. -/
theorem nonconstant_if_not_scc {K : Type} (E : K → K → Prop) (k k' : K)
    (hnot : ¬ Chain E k' k) :
    ∃ f : K → Int, (∀ a b, E a b → f a ≤ f b) ∧ f k ≠ f k' := by
  refine ⟨fun x => if Chain E k' x then 1 else 0, ?_, ?_⟩
  · intro a b hab
    show (if Chain E k' a then (1:Int) else 0) ≤ (if Chain E k' b then 1 else 0)
    by_cases ha : Chain E k' a
    · have hb : Chain E k' b := Chain.step ha hab
      rw [if_pos ha, if_pos hb]; exact Int.le_refl 1
    · rw [if_neg ha]
      by_cases hb : Chain E k' b
      · rw [if_pos hb]; decide
      · rw [if_neg hb]; exact Int.le_refl 0
  · show (if Chain E k' k then (1:Int) else 0) ≠ (if Chain E k' k' then 1 else 0)
    rw [if_neg hnot, if_pos (Chain.refl k')]
    decide

end ViaFutura

#print axioms ViaFutura.exact_covariance_gives_Su
#print axioms ViaFutura.exact_covariance_components
#print axioms ViaFutura.order_all_pairs_collapse
#print axioms ViaFutura.order_all_pairs_general
#print axioms ViaFutura.intervention_monotonicity_escapes
#print axioms ViaFutura.equality_on_fibre_steps_collapses
#print axioms ViaFutura.im_iff_edges
#print axioms ViaFutura.monotone_on_reach
#print axioms ViaFutura.constant_on_scc
#print axioms ViaFutura.nonconstant_if_not_scc
