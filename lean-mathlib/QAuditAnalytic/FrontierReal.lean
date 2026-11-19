import Mathlib

/-!
# FrontierReal.lean — the exact frontier of intervention monotonicity with real-valued degrees

Lean 4.24.0 with Mathlib v4.24.0.

The paper states the exact frontier of intervention monotonicity as Theorem `thm:frontier`
(Section `sec:im`). `ViaFutura.lean` (Lean 4 core, without Mathlib) checks, with degrees in
`Int`, part (a) for the intervention digraph (`im_iff_edges`) and parts (b) and (c) for an
abstract digraph (`constant_on_scc`, `nonconstant_if_not_scc`). This file proves the three
parts for degrees with values

* in any type with a relation `≤` (part (a), `im_iff_edges`),
* in any preorder (monotonicity along paths, `monotone_on_reach`),
* in any partial order (part (b), `constant_on_scc`),
* in any preorder with two values `w₀ < w₁` (part (c), `nonconstant_if_not_scc`),

and derives the statements with real-valued degrees as instances (`im_iff_edges_real`,
`monotone_on_reach_real`, `constant_on_scc_real`, `nonconstant_if_not_scc_real`).
`frontier_real` states the three parts together, in the order of quantifiers of the paper: for
all `T`, `Φ` and `κ`; in part (c), for all `s` and `s'` with `κ s` not reachable from `κ s'`,
there is a function on the classes (written `g` in the paper). `nonconstant_uniform` and
`frontier_c_uniform_real` show that one such function can be chosen from the digraph and the
class `k'` alone, for every class not reachable from `k'`. `escape_iff` and `escape_iff_real`
check the sentence after the theorem: a degree of the form `f ∘ κ` that satisfies `IM` and is
not constant on the realizations exists exactly when the intervention digraph on the realized
classes is not strongly connected; with no realizations the empty digraph counts as strongly
connected (`empty_domain_convention`).

The definitions `Chain` and `Edge` are copied verbatim from `ViaFutura.lean`, and
`chain_iff_reflTransGen` proves that `Chain` is Mathlib's `Relation.ReflTransGen`. The digraph
here has every class as a vertex, while the paper's has the realized classes `im κ`;
reachability between realized classes is the same in both (`chainIm_to_chain`,
`chain_to_chainIm`), and `frontier_paper_form` and `escape_paper_form` state the results with
the digraph on `im κ`.

The order hypotheses above are sufficient conditions. Part (b) uses only transitivity and
antisymmetry (`b_transitive_antisymmetric`), and neither can be dropped
(`b_needs_transitivity`, `b_needs_antisymmetry`). Part (c) in its `≠` form uses only two
distinct values `w₀ ≠ w₁` with `w₀ ≤ w₁` and reflexivity at them (`c_ne_of_two_values`; also
`c_ne_without_strict_pair`, in a preorder without a strict pair), and it fails in the discrete
order on two values, where no two distinct values are comparable (`c_fails_discrete_order`; the
general case is the same one-line argument and is not compiled here). No minimality is claimed
beyond these statements. The section `Example` checks non-vacuity on a three-class intervention
digraph.

What is not proved here. Part (c) gives the existence of a mathematical function that satisfies
`IM` and separates two classes. It does not identify that function with the unity degree `u`
of Q, it says nothing about which degree Q assigns, and it does not check that a physically
specified class of interventions, or the descriptor `Φ_Q` of Q, has the digraph assumed.
-/

namespace QAuditFrontier

/-! ## Definitions copied from `ViaFutura.lean` -/

/-- Reflexive–transitive closure of a step relation (verbatim from `ViaFutura.lean`). -/
inductive Chain {D : Type} (T : D → D → Prop) : D → D → Prop
  | refl (a : D) : Chain T a a
  | step {a b c : D} : Chain T a b → T b c → Chain T a c

/-- Edge `k → k'` when some `Φ`-raising intervention takes a `κ = k` realization to a
`κ = k'` one (verbatim from `ViaFutura.lean`). -/
def Edge {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V) (κ : D → K) (k k' : K) : Prop :=
  ∃ s t, T s t ∧ Φ s < Φ t ∧ κ s = k ∧ κ t = k'

/-- Intervention monotonicity `IM_𝒯` of a degree `u` (equation `eq:im` of the paper).
`ViaFutura.lean` writes this condition out instead of naming it. -/
def IM {D V : Type} {W : Type*} [LT V] [LE W] (T : D → D → Prop) (Φ : D → V) (u : D → W) :
    Prop :=
  ∀ s t, T s t → Φ s < Φ t → u s ≤ u t

/-- `Chain` is Mathlib's reflexive–transitive closure `Relation.ReflTransGen`. -/
theorem chain_iff_reflTransGen {D : Type} (T : D → D → Prop) (a b : D) :
    Chain T a b ↔ Relation.ReflTransGen T a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @step b c _ hT ih => exact Relation.ReflTransGen.tail ih hT
  · intro h
    induction h with
    | refl => exact Chain.refl a
    | tail _ hT ih => exact Chain.step ih hT

/-! ## The three parts for degrees in an arbitrary order -/

/-- Part (a), for degrees with values in any type with a relation `≤`: for a degree of the form
`f ∘ κ`, intervention monotonicity is exactly monotonicity of `f` along the edges of the
intervention digraph. -/
theorem im_iff_edges {D V K : Type} {W : Type*} [LT V] [LE W] (T : D → D → Prop) (Φ : D → V)
    (κ : D → K) (f : K → W) :
    (∀ s t, T s t → Φ s < Φ t → f (κ s) ≤ f (κ t)) ↔
      (∀ k k', Edge T Φ κ k k' → f k ≤ f k') := by
  constructor
  · rintro h k k' ⟨s, t, hT, hlt, rfl, rfl⟩
    exact h s t hT hlt
  · intro h s t hT hlt
    exact h _ _ ⟨s, t, hT, hlt, rfl, rfl⟩

/-- Any preorder: monotone along the edges implies monotone along paths. -/
theorem monotone_on_reach {K : Type} {W : Type*} [Preorder W] (E : K → K → Prop) (f : K → W)
    (h : ∀ k k', E k k' → f k ≤ f k') : ∀ k k', Chain E k k' → f k ≤ f k' := by
  intro k k' hc
  induction hc with
  | refl => exact le_refl _
  | @step b c _ hE ih => exact le_trans ih (h b c hE)

/-- Part (b), any partial order: a function monotone along the edges is constant on each
strongly connected component (on mutually reachable vertices). -/
theorem constant_on_scc {K : Type} {W : Type*} [PartialOrder W] (E : K → K → Prop)
    (f : K → W) (h : ∀ k k', E k k' → f k ≤ f k') (k k' : K)
    (h1 : Chain E k k') (h2 : Chain E k' k) : f k = f k' :=
  le_antisymm (monotone_on_reach E f h k k' h1) (monotone_on_reach E f h k' k h2)

/-- Part (c), any preorder with two values `w₀ < w₁`: if `k` is not reachable from `k'`, the
function equal to `w₁` on the vertices reachable from `k'` and to `w₀` elsewhere is monotone
along the edges, and its value at `k` is strictly below its value at `k'`. -/
theorem nonconstant_if_not_scc {K : Type} {W : Type*} [Preorder W] (E : K → K → Prop)
    {w₀ w₁ : W} (hw : w₀ < w₁) (k k' : K) (hnot : ¬ Chain E k' k) :
    ∃ f : K → W, (∀ a b, E a b → f a ≤ f b) ∧ f k < f k' := by
  classical
  refine ⟨fun x => if Chain E k' x then w₁ else w₀, ?_, ?_⟩
  · intro a b hab
    by_cases ha : Chain E k' a
    · have hb : Chain E k' b := Chain.step ha hab
      simp only [if_pos ha, if_pos hb, le_refl]
    · by_cases hb : Chain E k' b
      · simp only [if_neg ha, if_pos hb]
        exact hw.le
      · simp only [if_neg ha, if_neg hb, le_refl]
  · simp only [if_neg hnot, if_pos (Chain.refl k')]
    exact hw

/-- The sentence after the theorem, any partial order with two values `w₀ < w₁`: a degree of
the form `f ∘ κ` that satisfies `IM` and is not constant on the realizations exists if and only
if the intervention digraph on the realized classes is not strongly connected. -/
theorem escape_iff {D V K : Type} {W : Type*} [LT V] [PartialOrder W] {w₀ w₁ : W}
    (hw : w₀ < w₁) (T : D → D → Prop) (Φ : D → V) (κ : D → K) :
    (∃ f : K → W, IM T Φ (f ∘ κ) ∧ ∃ s s', f (κ s) ≠ f (κ s')) ↔
      ¬ ∀ s s', Chain (Edge T Φ κ) (κ s) (κ s') := by
  constructor
  · rintro ⟨f, hIM, s, s', hne⟩ hsc
    have hmono := (im_iff_edges T Φ κ f).1 hIM
    exact hne (constant_on_scc _ f hmono _ _ (hsc s s') (hsc s' s))
  · intro hns
    push_neg at hns
    obtain ⟨s, s', hc⟩ := hns
    obtain ⟨f, hmono, hlt⟩ := nonconstant_if_not_scc (Edge T Φ κ) hw (κ s') (κ s) hc
    exact ⟨f, (im_iff_edges T Φ κ f).2 hmono, s', s, ne_of_lt hlt⟩

/-! ## Real-valued degrees -/

/-- Part (a) with real-valued degrees (`ViaFutura.im_iff_edges` with `ℝ` in place of `Int`). -/
theorem im_iff_edges_real {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V) (κ : D → K)
    (f : K → ℝ) :
    (∀ s t, T s t → Φ s < Φ t → f (κ s) ≤ f (κ t)) ↔
      (∀ k k', Edge T Φ κ k k' → f k ≤ f k') :=
  im_iff_edges T Φ κ f

/-- Monotonicity along paths with real values (`ViaFutura.monotone_on_reach` with `ℝ`). -/
theorem monotone_on_reach_real {K : Type} (E : K → K → Prop) (f : K → ℝ)
    (h : ∀ k k', E k k' → f k ≤ f k') : ∀ k k', Chain E k k' → f k ≤ f k' :=
  monotone_on_reach E f h

/-- Part (b) with real values (`ViaFutura.constant_on_scc` with `ℝ` in place of `Int`). -/
theorem constant_on_scc_real {K : Type} (E : K → K → Prop) (f : K → ℝ)
    (h : ∀ k k', E k k' → f k ≤ f k') (k k' : K)
    (h1 : Chain E k k') (h2 : Chain E k' k) : f k = f k' :=
  constant_on_scc E f h k k' h1 h2

/-- Part (c) with real values (`ViaFutura.nonconstant_if_not_scc` with `ℝ` in place of `Int`). -/
theorem nonconstant_if_not_scc_real {K : Type} (E : K → K → Prop) (k k' : K)
    (hnot : ¬ Chain E k' k) :
    ∃ f : K → ℝ, (∀ a b, E a b → f a ≤ f b) ∧ f k ≠ f k' := by
  obtain ⟨f, hf, hlt⟩ := nonconstant_if_not_scc E (zero_lt_one : (0 : ℝ) < 1) k k' hnot
  exact ⟨f, hf, ne_of_lt hlt⟩

/-- Theorem `thm:frontier` with real-valued degrees, in the order of quantifiers of the paper:
for all `T`, `Φ` and `κ`,
(a) for every `f`, the degree `f ∘ κ` satisfies `IM` iff `f` is monotone along the edges of the
intervention digraph;
(b) every `f` monotone along the edges is constant on each strongly connected component;
(c) for all `s`, `s'` with `κ s` not reachable from `κ s'`, there is a function on the classes
(written `g` in the paper, bound as `f` below), monotone along the edges, that separates `κ s`
from `κ s'`; its composite with `κ` satisfies `IM` and separates `s` from `s'`. -/
theorem frontier_real {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V) (κ : D → K) :
    (∀ f : K → ℝ, IM T Φ (f ∘ κ) ↔ ∀ k k', Edge T Φ κ k k' → f k ≤ f k') ∧
    (∀ f : K → ℝ, (∀ k k', Edge T Φ κ k k' → f k ≤ f k') →
      ∀ k k', Chain (Edge T Φ κ) k k' → Chain (Edge T Φ κ) k' k → f k = f k') ∧
    (∀ s s', ¬ Chain (Edge T Φ κ) (κ s') (κ s) →
      ∃ f : K → ℝ, (∀ k k', Edge T Φ κ k k' → f k ≤ f k') ∧ f (κ s) ≠ f (κ s') ∧
        IM T Φ (f ∘ κ) ∧ (f ∘ κ) s ≠ (f ∘ κ) s') := by
  refine ⟨fun f => im_iff_edges T Φ κ f, fun f h k k' h1 h2 => constant_on_scc _ f h k k' h1 h2,
    ?_⟩
  intro s s' hnot
  obtain ⟨f, hmono, hne⟩ := nonconstant_if_not_scc_real (Edge T Φ κ) (κ s) (κ s') hnot
  exact ⟨f, hmono, hne, (im_iff_edges T Φ κ f).2 hmono, hne⟩

/-- `escape_iff` with real-valued degrees. -/
theorem escape_iff_real {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V) (κ : D → K) :
    (∃ f : K → ℝ, IM T Φ (f ∘ κ) ∧ ∃ s s', f (κ s) ≠ f (κ s')) ↔
      ¬ ∀ s s', Chain (Edge T Φ κ) (κ s) (κ s') :=
  escape_iff (zero_lt_one : (0 : ℝ) < 1) T Φ κ

/-! ## Part (c) with one function for a fixed class

The function of part (c) can be chosen from the digraph and the class `k'` alone: the
indicator of the vertices reachable from `k'` separates `k'` from every vertex that is not
reachable from it. -/

/-- Part (c), with one function for a fixed vertex `k'`, any preorder with two values
`w₀ < w₁`: for a vertex `k'` of a digraph `E` there is a function `g`, monotone along the
edges, whose value at every vertex not reachable from `k'` is strictly below its value at `k'`.
The function depends only on `E` and `k'`. -/
theorem nonconstant_uniform {K : Type} {W : Type*} [Preorder W] (E : K → K → Prop)
    {w₀ w₁ : W} (hw : w₀ < w₁) (k' : K) :
    ∃ g : K → W, (∀ a b, E a b → g a ≤ g b) ∧ ∀ k, ¬ Chain E k' k → g k < g k' := by
  classical
  refine ⟨fun x => if Chain E k' x then w₁ else w₀, ?_, ?_⟩
  · intro a b hab
    by_cases ha : Chain E k' a
    · have hb : Chain E k' b := Chain.step ha hab
      simp only [if_pos ha, if_pos hb, le_refl]
    · by_cases hb : Chain E k' b
      · simp only [if_neg ha, if_pos hb]
        exact hw.le
      · simp only [if_neg ha, if_neg hb, le_refl]
  · intro k hnot
    simp only [if_neg hnot, if_pos (Chain.refl k')]
    exact hw

/-- Part (c) of `frontier_real` with one real function for a fixed class `k'`: for all `T`,
`Φ`, `κ` and `k'`, some real `g` on the classes, chosen from the intervention digraph and `k'`
(the indicator of the classes reachable from `k'`), is monotone along the edges, its composite
with `κ` satisfies `IM`, and it separates `k'` from every class not reachable from `k'`. -/
theorem frontier_c_uniform_real {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V)
    (κ : D → K) (k' : K) :
    ∃ g : K → ℝ, (∀ a b, Edge T Φ κ a b → g a ≤ g b) ∧ IM T Φ (g ∘ κ) ∧
      ∀ k, ¬ Chain (Edge T Φ κ) k' k → g k ≠ g k' := by
  obtain ⟨g, hmono, hlt⟩ := nonconstant_uniform (Edge T Φ κ) (zero_lt_one : (0 : ℝ) < 1) k'
  exact ⟨g, hmono, (im_iff_edges T Φ κ g).2 hmono, fun k hk => ne_of_lt (hlt k hk)⟩

/-! ## The digraph on the realized classes, as in the paper

The paper's intervention digraph has the realized classes `im κ` as vertices; the statements
above take every class as a vertex. A class outside `im κ` has no edges, so reachability
between realized classes is the same in both digraphs, and the three parts and the sentence
after the theorem hold with the digraph on `im κ`. -/

/-- The vertex set of the paper's intervention digraph: the realized classes `im κ`. -/
abbrev Realized {D K : Type} (κ : D → K) : Type := {k : K // ∃ s, κ s = k}

/-- The paper's intervention digraph, on `im κ` only. -/
def EdgeIm {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V) (κ : D → K)
    (a b : Realized κ) : Prop :=
  Edge T Φ κ a.1 b.1

theorem chainIm_to_chain {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V) (κ : D → K)
    (a b : Realized κ) (h : Chain (EdgeIm T Φ κ) a b) : Chain (Edge T Φ κ) a.1 b.1 := by
  induction h with
  | refl => exact Chain.refl _
  | @step y z _ hE ih => exact Chain.step ih hE

theorem chain_to_chainIm {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V) (κ : D → K)
    (k x : K) (h : Chain (Edge T Φ κ) k x) :
    ∀ (hk : ∃ s, κ s = k) (hx : ∃ s, κ s = x), Chain (EdgeIm T Φ κ) ⟨k, hk⟩ ⟨x, hx⟩ := by
  induction h with
  | refl => intro hk hx; exact Chain.refl _
  | @step y z _ hE ih =>
    intro hk hz
    obtain ⟨s, t, hT, hlt, hs, ht⟩ := hE
    exact Chain.step (ih hk ⟨s, hs⟩) ⟨s, t, hT, hlt, hs, ht⟩

/-- Theorem `thm:frontier` (a), (b), (c) with real-valued degrees and the digraph on `im κ`, as in
the paper, derived from `frontier_real`. -/
theorem frontier_paper_form {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V) (κ : D → K) :
    (∀ f : K → ℝ, IM T Φ (f ∘ κ) ↔ ∀ a b : Realized κ, EdgeIm T Φ κ a b → f a.1 ≤ f b.1) ∧
    (∀ f : K → ℝ, (∀ a b : Realized κ, EdgeIm T Φ κ a b → f a.1 ≤ f b.1) →
      ∀ a b : Realized κ, Chain (EdgeIm T Φ κ) a b → Chain (EdgeIm T Φ κ) b a →
        f a.1 = f b.1) ∧
    (∀ s s' : D, ¬ Chain (EdgeIm T Φ κ) ⟨κ s', s', rfl⟩ ⟨κ s, s, rfl⟩ →
      ∃ f : K → ℝ, (∀ a b : Realized κ, EdgeIm T Φ κ a b → f a.1 ≤ f b.1) ∧
        f (κ s) ≠ f (κ s') ∧ IM T Φ (f ∘ κ) ∧ (f ∘ κ) s ≠ (f ∘ κ) s') := by
  obtain ⟨hA, hB, hC⟩ := frontier_real T Φ κ
  have medges : ∀ f : K → ℝ, (∀ a b : Realized κ, EdgeIm T Φ κ a b → f a.1 ≤ f b.1) ↔
      (∀ k k', Edge T Φ κ k k' → f k ≤ f k') := by
    intro f
    constructor
    · intro h k k' hE
      obtain ⟨s, t, hT, hlt, hs, ht⟩ := hE
      exact h ⟨k, s, hs⟩ ⟨k', t, ht⟩ ⟨s, t, hT, hlt, hs, ht⟩
    · intro h a b hE
      exact h a.1 b.1 hE
  refine ⟨fun f => (hA f).trans (medges f).symm, ?_, ?_⟩
  · intro f hf a b hab hba
    exact hB f ((medges f).1 hf) a.1 b.1 (chainIm_to_chain T Φ κ a b hab)
      (chainIm_to_chain T Φ κ b a hba)
  · intro s s' hnot
    have hnot' : ¬ Chain (Edge T Φ κ) (κ s') (κ s) := fun h =>
      hnot (chain_to_chainIm T Φ κ (κ s') (κ s) h ⟨s', rfl⟩ ⟨s, rfl⟩)
    obtain ⟨f, hm, hne, hIM, hne'⟩ := hC s s' hnot'
    exact ⟨f, (medges f).2 hm, hne, hIM, hne'⟩

/-- The sentence after the theorem with the digraph on `im κ`: a real degree `f ∘ κ` that
satisfies `IM` and is not constant exists iff the digraph on `im κ` is not strongly connected. -/
theorem escape_paper_form {D V K : Type} [LT V] (T : D → D → Prop) (Φ : D → V) (κ : D → K) :
    (∃ f : K → ℝ, IM T Φ (f ∘ κ) ∧ ∃ s s', f (κ s) ≠ f (κ s')) ↔
      ¬ ∀ a b : Realized κ, Chain (EdgeIm T Φ κ) a b := by
  rw [escape_iff_real T Φ κ]
  constructor
  · intro h hall
    exact h (fun s s' => chainIm_to_chain T Φ κ ⟨κ s, s, rfl⟩ ⟨κ s', s', rfl⟩ (hall _ _))
  · intro h hall
    apply h
    intro s s'
    obtain ⟨k, a, rfl⟩ := s
    obtain ⟨k', b, rfl⟩ := s'
    exact chain_to_chainIm T Φ κ (κ a) (κ b) (hall a b) ⟨a, rfl⟩ ⟨b, rfl⟩

/-- Degenerate domain: with no realizations, the right side of `escape_iff_real` is false,
i.e. the empty digraph is counted as strongly connected (and no escape exists). -/
theorem empty_domain_convention (T : Empty → Empty → Prop) (Φ : Empty → ℝ) (κ : Empty → Unit) :
    (¬ ¬ ∀ s s', Chain (Edge T Φ κ) (κ s) (κ s')) ∧
    ¬ ∃ f : Unit → ℝ, IM T Φ (f ∘ κ) ∧ ∃ s s', f (κ s) ≠ f (κ s') :=
  ⟨fun h => h (fun s => s.elim), fun ⟨_, _, s, _⟩ => s.elim⟩

/-! ## Which order hypotheses the three parts use

The parts are proved above for degrees in a type with a relation `≤` (a), in a partial order
(b) and in a preorder with two values `w₀ < w₁` (c). These are sufficient conditions. The
statements below show what the proofs of (b) and (c) use and that some hypotheses cannot be
dropped; they do not show that any set of hypotheses is the least one. -/

/-- Monotone along nonempty paths, for a merely transitive relation `le`. -/
theorem mono_pos {K W : Type} (le : W → W → Prop) (htr : ∀ a b c, le a b → le b c → le a c)
    (E : K → K → Prop) (f : K → W) (h : ∀ a b, E a b → le (f a) (f b)) :
    ∀ k k', Chain E k k' → k = k' ∨ le (f k) (f k') := by
  intro k k' hc
  induction hc with
  | refl => exact Or.inl rfl
  | @step b c _ hE ih =>
    cases ih with
    | inl heq => subst heq; exact Or.inr (h _ _ hE)
    | inr hle => exact Or.inr (htr _ _ _ hle (h _ _ hE))

/-- Part (b) for a relation `le` that is transitive and antisymmetric: reflexivity is not used. -/
theorem b_transitive_antisymmetric {K W : Type} (le : W → W → Prop)
    (htr : ∀ a b c, le a b → le b c → le a c) (hanti : ∀ a b, le a b → le b a → a = b)
    (E : K → K → Prop) (f : K → W) (h : ∀ a b, E a b → le (f a) (f b)) (k k' : K)
    (h1 : Chain E k k') (h2 : Chain E k' k) : f k = f k' := by
  cases mono_pos le htr E f h k k' h1 with
  | inl heq => rw [heq]
  | inr a =>
    cases mono_pos le htr E f h k' k h2 with
    | inl heq => rw [heq]
    | inr b => exact hanti _ _ a b

/-- Transitivity cannot be dropped from (b), even keeping reflexivity and antisymmetry:
`cyc` is a reflexive, antisymmetric, non-transitive cyclic relation on `Fin 3`; on the 3-cycle
digraph `E3`, `f = id` is monotone along the edges for `cyc`, the vertices `0` and `1` are
mutually reachable, and `f 0 ≠ f 1`. -/
def cyc (a b : Fin 3) : Prop :=
  a = b ∨ (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 0)
def E3 (a b : Fin 3) : Prop := (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 2) ∨ (a.val = 2 ∧ b.val = 0)
instance : DecidableRel cyc := fun a b => by unfold cyc; infer_instance
instance : DecidableRel E3 := fun a b => by unfold E3; infer_instance

theorem b_needs_transitivity :
    (∀ a, cyc a a) ∧ (∀ a b, cyc a b → cyc b a → a = b) ∧ ¬ (∀ a b c, cyc a b → cyc b c → cyc a c) ∧
    (∀ a b, E3 a b → cyc (id a) (id b)) ∧ Chain E3 0 1 ∧ Chain E3 1 0 ∧ (id (0 : Fin 3) ≠ id 1) := by
  refine ⟨fun a => Or.inl rfl, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · decide
  · intro htr
    have h02 : cyc 0 2 := htr 0 1 2 (by decide) (by decide)
    exact absurd h02 (by decide)
  · intro a b h; exact Or.inr h
  · exact Chain.step (b := (0 : Fin 3)) (Chain.refl 0) (by decide)
  · exact Chain.step (b := (2 : Fin 3)) (Chain.step (b := (1 : Fin 3)) (Chain.refl 1) (by decide)) (by decide)

/-- `Bool` with the preorder in which every value is below every other one: reflexive and
transitive, not antisymmetric, and without a strict pair. -/
def CodiscreteBool := Bool

instance : Preorder CodiscreteBool where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

/-- Antisymmetry cannot be dropped from (b): in the preorder `CodiscreteBool`, which is not a
partial order, a function monotone along the edges is not constant on a strongly connected
component. -/
theorem b_needs_antisymmetry :
    ∃ (E : Bool → Bool → Prop) (f : Bool → CodiscreteBool),
      (∀ k k', E k k' → f k ≤ f k') ∧ Chain E false true ∧ Chain E true false ∧
        f false ≠ f true := by
  refine ⟨fun _ _ => True, fun b => b, fun _ _ _ => trivial,
    Chain.step (Chain.refl false) trivial, Chain.step (Chain.refl true) trivial, ?_⟩
  exact Bool.false_ne_true

/-- Part (c) in its `≠` form for a relation `le` with two distinct values `w₀ ≠ w₁` such that
`le w₀ w₀`, `le w₁ w₁` and `le w₀ w₁`: transitivity, antisymmetry and a strict pair are not
used. -/
theorem c_ne_of_two_values {K W : Type} (le : W → W → Prop) {w₀ w₁ : W} (h00 : le w₀ w₀) (h11 : le w₁ w₁)
    (h01 : le w₀ w₁) (hne : w₀ ≠ w₁) (E : K → K → Prop) (k k' : K) (hnot : ¬ Chain E k' k) :
    ∃ f : K → W, (∀ a b, E a b → le (f a) (f b)) ∧ f k ≠ f k' := by
  have dec : ∀ x, Decidable (Chain E k' x) := fun _ => Classical.propDecidable _
  refine ⟨fun x => if Chain E k' x then w₁ else w₀, ?_, ?_⟩
  · intro a b hab
    by_cases ha : Chain E k' a
    · have hb : Chain E k' b := Chain.step ha hab
      simp only [if_pos ha, if_pos hb]; exact h11
    · by_cases hb : Chain E k' b
      · simp only [if_neg ha, if_pos hb]; exact h01
      · simp only [if_neg ha, if_neg hb]; exact h00
  · simp only [if_neg hnot, if_pos (Chain.refl k')]; exact hne

/-- `CodiscreteBool` has no strict pair. -/
theorem codis_no_strict_pair : ¬ ∃ w₀ w₁ : CodiscreteBool, w₀ < w₁ := by
  rintro ⟨w₀, w₁, h⟩
  exact (lt_iff_le_not_ge.mp h).2 trivial

/-- Part (c) in its `≠` form holds in `CodiscreteBool`, which has no strict pair: the hypothesis
`w₀ < w₁` of `nonconstant_if_not_scc` is sufficient, not necessary among preorders. -/
theorem c_ne_without_strict_pair {K : Type} (E : K → K → Prop) (k k' : K)
    (hnot : ¬ Chain E k' k) :
    ∃ f : K → CodiscreteBool, (∀ a b, E a b → f a ≤ f b) ∧ f k ≠ f k' := by
  classical
  refine ⟨fun x => (decide (Chain E k' x) : Bool), fun _ _ _ => trivial, ?_⟩
  show (decide (Chain E k' k) : Bool) ≠ decide (Chain E k' k')
  rw [decide_eq_false hnot, decide_eq_true (Chain.refl k')]
  exact Bool.false_ne_true

/-- `Bool` with the discrete partial order: `x ≤ y` iff `x = y`, so that no two distinct values
are comparable. -/
def DiscreteBool := Bool

instance : PartialOrder DiscreteBool where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h _ := h

/-- Part (c) fails in the discrete order on two values, where no two distinct values are
comparable: with the single edge `false → true`, `false` is not reachable from `true`, yet every
function into the discrete order `DiscreteBool` that is monotone along the edges takes the same
value at `false` and `true`. -/
theorem c_fails_discrete_order :
    let E : Bool → Bool → Prop := fun a b => a = false ∧ b = true
    ¬ Chain E true false ∧
      ∀ f : Bool → DiscreteBool, (∀ a b, E a b → f a ≤ f b) → f false = f true := by
  intro E
  refine ⟨?_, fun f hf => hf false true ⟨rfl, rfl⟩⟩
  have key : ∀ x, Chain E true x → x = true := by
    intro x h
    induction h with
    | refl => rfl
    | @step b c _ hE ih =>
      subst ih
      exact absurd hE.1 (by decide)
  intro h
  exact absurd (key false h) (by decide)

/-! ## Non-vacuity: a three-class intervention digraph

One bearer with four realizations `0, 1, 2, 3`, a real descriptor `Φ s = s`, interventions
from each realization to the next (so each raises `Φ`), and coexperience classes
`κ = (0, 1, 0, 2)`. The intervention digraph on the classes has the edges `0 → 1`, `1 → 0` and
`0 → 2`: the classes `0` and `1` form a strongly connected component, and neither is reachable
from class `2`. -/

namespace Example

/-- A real descriptor that every intervention raises. -/
noncomputable def Φex : Fin 4 → ℝ := fun s => (s.val : ℝ)

/-- The coexperience classes of the four realizations. -/
def κex : Fin 4 → Fin 3 := ![0, 1, 0, 2]

/-- The interventions: from each realization to the next. -/
def Tex : Fin 4 → Fin 4 → Prop := fun s t => t.val = s.val + 1

/-- The intervention digraph has exactly the edges `0 → 1`, `1 → 0` and `0 → 2`. -/
theorem edge_iff (k k' : Fin 3) :
    Edge Tex Φex κex k k' ↔ (k = 0 ∧ k' = 1) ∨ (k = 1 ∧ k' = 0) ∨ (k = 0 ∧ k' = 2) := by
  constructor
  · rintro ⟨s, t, hT, -, rfl, rfl⟩
    fin_cases s <;> fin_cases t <;> simp_all [Tex, κex]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨0, 1, rfl, by norm_num [Φex], rfl, rfl⟩
    · exact ⟨1, 2, rfl, by norm_num [Φex], rfl, rfl⟩
    · exact ⟨2, 3, rfl, by norm_num [Φex], rfl, rfl⟩

/-- Only class `2` is reachable from class `2`. -/
theorem reach_from_two (x : Fin 3) (h : Chain (Edge Tex Φex κex) 2 x) : x = 2 := by
  induction h with
  | refl => rfl
  | @step b c _ hE ih =>
    subst ih
    rcases (edge_iff 2 c).1 hE with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

/-- Non-vacuity of parts (b) and (c) with real degrees: classes `0` and `1` are mutually
reachable and neither is reachable from class `2`; every real degree that satisfies `IM`
takes the same value on classes `0` and `1`; and some real degree that satisfies `IM` takes
the same value on classes `0` and `1` and a different value on class `2`, so that it differs
on the realizations `3` and `0`. -/
theorem nonvacuous :
    (Chain (Edge Tex Φex κex) 0 1 ∧ Chain (Edge Tex Φex κex) 1 0) ∧
    (¬ Chain (Edge Tex Φex κex) 2 0 ∧ ¬ Chain (Edge Tex Φex κex) 2 1) ∧
    (∀ f : Fin 3 → ℝ, IM Tex Φex (f ∘ κex) → f 0 = f 1) ∧
    (∃ f : Fin 3 → ℝ, IM Tex Φex (f ∘ κex) ∧ f 0 = f 1 ∧ f 2 ≠ f 0 ∧
      (f ∘ κex) 3 ≠ (f ∘ κex) 0) := by
  have e01 : Edge Tex Φex κex 0 1 := (edge_iff 0 1).2 (Or.inl ⟨rfl, rfl⟩)
  have e10 : Edge Tex Φex κex 1 0 := (edge_iff 1 0).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have c01 : Chain (Edge Tex Φex κex) 0 1 := Chain.step (Chain.refl 0) e01
  have c10 : Chain (Edge Tex Φex κex) 1 0 := Chain.step (Chain.refl 1) e10
  have n20 : ¬ Chain (Edge Tex Φex κex) 2 0 := fun h => absurd (reach_from_two 0 h) (by decide)
  have n21 : ¬ Chain (Edge Tex Φex κex) 2 1 := fun h => absurd (reach_from_two 1 h) (by decide)
  obtain ⟨hA, hB, hC⟩ := frontier_real Tex Φex κex
  have forced : ∀ f : Fin 3 → ℝ, IM Tex Φex (f ∘ κex) → f 0 = f 1 := fun f hf =>
    hB f ((hA f).1 hf) 0 1 c01 c10
  refine ⟨⟨c01, c10⟩, ⟨n20, n21⟩, forced, ?_⟩
  -- part (c) with `s = 0` (class `0`) and `s' = 3` (class `2`)
  obtain ⟨f, -, hne, hIM, -⟩ := hC 0 3 n20
  exact ⟨f, hIM, forced f hIM, fun h => hne h.symm, fun h => hne h.symm⟩

/-- An explicit real degree with an irrational value: in the model above, `f = (0, 0, π)`
satisfies `IM`, takes the same value on classes `0` and `1`, and a different value on
class `2`. -/
theorem pi_degree :
    IM Tex Φex ((![0, 0, Real.pi] : Fin 3 → ℝ) ∘ κex) ∧
      (![0, 0, Real.pi] : Fin 3 → ℝ) 0 = (![0, 0, Real.pi] : Fin 3 → ℝ) 1 ∧
      (![0, 0, Real.pi] : Fin 3 → ℝ) 2 ≠ (![0, 0, Real.pi] : Fin 3 → ℝ) 0 := by
  refine ⟨(im_iff_edges Tex Φex κex (![0, 0, Real.pi] : Fin 3 → ℝ)).2 ?_, by simp, ?_⟩
  · intro k k' hE
    rcases (edge_iff k k').1 hE with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp
    · simp
    · simp [Real.pi_pos.le]
  · simp [Real.pi_ne_zero]

end Example

end QAuditFrontier

#print axioms QAuditFrontier.chain_iff_reflTransGen
#print axioms QAuditFrontier.im_iff_edges
#print axioms QAuditFrontier.monotone_on_reach
#print axioms QAuditFrontier.constant_on_scc
#print axioms QAuditFrontier.nonconstant_if_not_scc
#print axioms QAuditFrontier.escape_iff
#print axioms QAuditFrontier.im_iff_edges_real
#print axioms QAuditFrontier.monotone_on_reach_real
#print axioms QAuditFrontier.constant_on_scc_real
#print axioms QAuditFrontier.nonconstant_if_not_scc_real
#print axioms QAuditFrontier.frontier_real
#print axioms QAuditFrontier.escape_iff_real
#print axioms QAuditFrontier.nonconstant_uniform
#print axioms QAuditFrontier.frontier_c_uniform_real
#print axioms QAuditFrontier.chainIm_to_chain
#print axioms QAuditFrontier.chain_to_chainIm
#print axioms QAuditFrontier.frontier_paper_form
#print axioms QAuditFrontier.escape_paper_form
#print axioms QAuditFrontier.empty_domain_convention
#print axioms QAuditFrontier.mono_pos
#print axioms QAuditFrontier.b_transitive_antisymmetric
#print axioms QAuditFrontier.b_needs_transitivity
#print axioms QAuditFrontier.b_needs_antisymmetry
#print axioms QAuditFrontier.c_ne_of_two_values
#print axioms QAuditFrontier.codis_no_strict_pair
#print axioms QAuditFrontier.c_ne_without_strict_pair
#print axioms QAuditFrontier.c_fails_discrete_order
#print axioms QAuditFrontier.Example.edge_iff
#print axioms QAuditFrontier.Example.reach_from_two
#print axioms QAuditFrontier.Example.nonvacuous
#print axioms QAuditFrontier.Example.pi_degree
