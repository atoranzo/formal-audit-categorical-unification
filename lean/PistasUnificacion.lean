/-!
# PistasUnificacion.lean — four routes towards a weak, structural unification
# that respects the counterexamples of `UnificacionCat.lean` and `IntentoSu.lean`.

Lean 4 core (4.24.0), no Mathlib. Only combinatorial and logical parts are here;
the real-analytic parts (the Gaussian functional J, its Cheeger-type bounds) are
proved on paper (Sections 3 and 4 of the paper) and checked numerically by the
scripts in `python/numeric/` of the archive that accompanies the paper.

* Route 2 (lax 2-cell): a universal (broadcast) vertex forces connectivity for
  every n (`universal_connected`); for n = 3 connectivity and broadcast coincide
  (`n3_equiv`); for n = 4 exactly 15 labelled connected graphs lack a universal
  vertex (`n4_count`), so the 2-cell is strict from n = 4 on.
* Route 1 (defect on the tensor ideal): a disjoint union (tensor) of two nonempty
  systems has no universal vertex (`tensor_no_universal`).
* Route 3 (selection on fibres): a section of Φ yields the factor u ∘ s ∘ Φ iff
  S_u already holds (`section_factor_iff`); fibre purity plus OI gives S_u
  (`purity_gives_Su`), and a single non-isomorphic pair in a fibre (as Rob
  provides) destroys purity (`witness_breaks_purity`).
* Route 4: on the connected domain the presence predicate of integration is
  constant, so a presence-level 2-cell into it is trivial (`connected_domain_trivial`).
-/

namespace Pistas

/-! ## Route 2: broadcast ⇒ connectivity, strict from n = 4 -/

/-- `w` is a universal (broadcast) vertex of a symmetric adjacency. -/
def Universal {n : Nat} (adj : Fin n → Fin n → Bool) (w : Fin n) : Prop :=
  ∀ v, v ≠ w → adj w v = true

/-- Reachability within two steps (enough for the statement below). -/
def Reach2 {n : Nat} (adj : Fin n → Fin n → Bool) (i j : Fin n) : Prop :=
  i = j ∨ adj i j = true ∨ ∃ k, adj i k = true ∧ adj k j = true

theorem universal_connected {n : Nat} (adj : Fin n → Fin n → Bool)
    (hsym : ∀ i j, adj i j = adj j i) (w : Fin n) (hw : Universal adj w) :
    ∀ i j, Reach2 adj i j := by
  intro i j
  by_cases hij : i = j
  · exact Or.inl hij
  by_cases hi : i = w
  · subst hi
    exact Or.inr (Or.inl (hw j (fun h => hij h.symm)))
  by_cases hj : j = w
  · subst hj
    refine Or.inr (Or.inl ?_)
    rw [hsym]; exact hw i hi
  · refine Or.inr (Or.inr ⟨w, ?_, hw j hj⟩)
    rw [hsym]; exact hw i hi

/-- Graphs on `Fin n` given by the bits of a natural number over the ordered pairs i<j. -/
def pairIndex (n : Nat) (i j : Nat) : Nat :=
  -- index of the pair {i,j}, i<j, in lexicographic order
  (List.range i).foldl (fun acc a => acc + (n - 1 - a)) 0 + (j - i - 1)

def edge (n bits : Nat) (i j : Fin n) : Bool :=
  if i.val < j.val then (bits >>> pairIndex n i.val j.val) % 2 == 1
  else if j.val < i.val then (bits >>> pairIndex n j.val i.val) % 2 == 1
  else false

/-- Full connectivity by iterated reachability (n rounds suffice). -/
def reachable (n bits : Nat) (src : Fin n) : List (Fin n) :=
  (List.range n).foldl
    (fun seen _ => (List.finRange n).filter
      (fun v => seen.contains v || seen.any (fun u => edge n bits u v)))
    [src]

def connectedB (n bits : Nat) : Bool :=
  match n with
  | 0 => true
  | m + 1 => (List.finRange (m + 1)).all (fun v => (reachable (m + 1) bits ⟨0, Nat.succ_pos m⟩).contains v)

def universalB (n bits : Nat) : Bool :=
  (List.finRange n).any (fun w => (List.finRange n).all (fun v => v == w || edge n bits w v))

/-- n = 3: a graph is connected iff it has a universal vertex (all 8 graphs). -/
theorem n3_equiv : (List.range 8).all (fun b => connectedB 3 b == universalB 3 b) = true := by
  decide

/-- n = 4: exactly 15 labelled graphs are connected without a universal vertex,
and no graph has a universal vertex without being connected. -/
theorem n4_count :
    ((List.range 64).filter (fun b => connectedB 4 b && !universalB 4 b)).length = 15 ∧
    ((List.range 64).filter (fun b => universalB 4 b && !connectedB 4 b)).length = 0 := by
  decide


/-! ## Route 2, general n: the path graph P_n is connected and has no broadcast
vertex for every n ≥ 4, so the lax 2-cell is strict for all n ≥ 4 (not only 4, 5). -/

/-- Path graph on `Fin n`: i ~ j iff they differ by one. -/
def pathAdj (n : Nat) (i j : Fin n) : Bool := i.val + 1 == j.val || j.val + 1 == i.val

/-- Reachability by finite chains of edges. -/
inductive Reach {n : Nat} (adj : Fin n → Fin n → Bool) : Fin n → Fin n → Prop
  | refl (a : Fin n) : Reach adj a a
  | step {a b c : Fin n} : Reach adj a b → adj b c = true → Reach adj a c

theorem path_reach_from_zero (n : Nat) (hn : 0 < n) :
    ∀ k : Nat, (hk : k < n) → Reach (pathAdj n) ⟨0, hn⟩ ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero => intro hk; exact Reach.refl _
  | succ m ih =>
    intro hk
    have hm : m < n := Nat.lt_of_succ_lt hk
    refine Reach.step (ih hm) ?_
    simp [pathAdj]

theorem path_no_universal (n : Nat) (hn : 4 ≤ n) :
    ¬ ∃ w : Fin n, ∀ v : Fin n, v ≠ w → pathAdj n w v = true := by
  intro ⟨w, hw⟩
  by_cases hsmall : w.val ≤ 1
  · have hv : w.val + 2 < n := by omega
    have h := hw ⟨w.val + 2, hv⟩ (by intro h; have := congrArg Fin.val h; simp at this)
    simp [pathAdj] at h
    omega
  · have hv : w.val - 2 < n := by omega
    have h := hw ⟨w.val - 2, hv⟩ (by intro h; have := congrArg Fin.val h; simp at this; omega)
    simp [pathAdj] at h
    omega

/-! ## Route 1: no broadcast vertex in a tensor product -/

/-- Disjoint union (tensor) of two systems: no edges across. -/
def tensorAdj {m n : Nat} (a : Fin m → Fin m → Bool) (b : Fin n → Fin n → Bool) :
    (Fin m ⊕ Fin n) → (Fin m ⊕ Fin n) → Bool
  | .inl i, .inl j => a i j
  | .inr i, .inr j => b i j
  | _, _ => false

theorem tensor_no_universal {m n : Nat} (a : Fin m → Fin m → Bool) (b : Fin n → Fin n → Bool)
    (hm : 0 < m) (hn : 0 < n) :
    ¬ ∃ w, ∀ v, v ≠ w → tensorAdj a b w v = true := by
  intro ⟨w, hw⟩
  cases w with
  | inl i =>
    have h := hw (.inr ⟨0, hn⟩) (by intro h; cases h)
    simp [tensorAdj] at h
  | inr i =>
    have h := hw (.inl ⟨0, hm⟩) (by intro h; cases h)
    simp [tensorAdj] at h

/-! ## Route 3: a section of Φ does not give S_u -/

def Suff {D V U : Type} (Φ : D → V) (u : D → U) : Prop := ∀ s t, Φ s = Φ t → u s = u t

/-- For any section `sec` of Φ (Φ (sec (Φ x)) = Φ x), the representative values define
a factor of `u` through Φ iff S_u already holds. Selecting representatives adds nothing. -/
theorem section_factor_iff {D V U : Type} (Φ : D → V) (u : D → U) (sec : V → D)
    (hsec : ∀ x, Φ (sec (Φ x)) = Φ x) :
    (∀ x, u x = u (sec (Φ x))) ↔ Suff Φ u := by
  constructor
  · intro h s t hst
    rw [h s, h t, hst]
  · intro h x
    exact h x (sec (Φ x)) (hsec x).symm

/-- Fibre purity (one isomorphism class per fibre) plus OI gives S_u. -/
theorem purity_gives_Su {D V U : Type} (Φ : D → V) (u : D → U) (iso : D → D → Prop)
    (hpure : ∀ s t, Φ s = Φ t → iso s t) (hOI : ∀ s t, iso s t → u s = u t) : Suff Φ u :=
  fun s t h => hOI s t (hpure s t h)

/-- One non-isomorphic pair in a fibre (what Rob and the continuum theorem provide)
destroys fibre purity. -/
theorem witness_breaks_purity {D V : Type} (Φ : D → V) (iso : D → D → Prop)
    (s t : D) (hΦ : Φ s = Φ t) (hni : ¬ iso s t) : ¬ ∀ x y, Φ x = Φ y → iso x y :=
  fun h => hni (h s t hΦ)

/-! ## Route 4: on the connected domain the integration predicate is constant -/

/-- On any domain where integration positivity holds everywhere, a presence-level
2-cell `P ≤ Ipos` holds for every predicate `P`: it carries no information. -/
theorem connected_domain_trivial {S : Type} (dom : S → Prop) (Ipos P : S → Bool)
    (hconst : ∀ x, dom x → Ipos x = true) : ∀ x, dom x → (P x = true → Ipos x = true) :=
  fun x hx _ => hconst x hx

end Pistas

#print axioms Pistas.universal_connected
#print axioms Pistas.n3_equiv
#print axioms Pistas.n4_count
#print axioms Pistas.path_reach_from_zero
#print axioms Pistas.path_no_universal
#print axioms Pistas.tensor_no_universal
#print axioms Pistas.section_factor_iff
#print axioms Pistas.purity_gives_Su
#print axioms Pistas.witness_breaks_purity
#print axioms Pistas.connected_domain_trivial
