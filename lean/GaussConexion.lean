/-!
# GaussConexion.lean — the logical skeleton of the connections between the
# restricted Gaussian family F0 and the main theorems of the paper
# (connections (i)-(v) of its Section 5).

Lean 4 core (4.24.0), no Mathlib. The real-analytic and measure-theoretic facts
about F0 (J = ½ log(1+k), the uniqueness of the minimizer, the mutual absolute
continuity of finite windows, the chain argument with r(k,p)) are established in
Section 5 of the paper, by written proofs and by exact SymPy checks (the scripts in
`python/exact/` of the archive that accompanies the paper). They are NOT proved
here. What is proved here is only the abstract logic they instantiate.

* `plateau_product`: if every history is realized with every law (a product
  domain, the idealized form of a common full support), u depends only on the
  history, and S holds for a law-level descriptor, then u is constant.
* `aligned_premise_iff`: if Φ = g ∘ k with g injective, then S for k ("u depends
  only on k", the premise IPS_K) is equivalent to S for Φ: a reformulation.
* `n2_equiv`: for n = 2 a graph is connected iff it has a universal vertex
  (together with `n3_equiv` of `PistasUnificacion.lean`: there is no band below n = 4).
* `f0_hub_readings`: for the one-way coupling of F0, the undirected support has a
  universal vertex, while no unit is coupled in both directions.
-/

namespace GaussConexion

/-- S for a descriptor Φ: equal descriptor values force equal degree. -/
def Suff {D V U : Type} (Φ : D → V) (u : D → U) : Prop :=
  ∀ s t, Φ s = Φ t → u s = u t

/-- Product domain (every history `h` realized with every law `L`), degree that
depends only on the history, S for a law-level descriptor: the degree is constant.
Two steps of the co-occurrence relation: same law, then same history. -/
theorem plateau_product {L H V U : Type} (F : L → V) (Uh : H → U) (u : L × H → U)
    (hfac : ∀ x, u x = Uh x.2) (hS : Suff (fun x : L × H => F x.1) u) :
    ∀ a b : L × H, u a = u b := by
  intro a b
  have h1 : u a = u (a.1, b.2) := hS a (a.1, b.2) rfl
  have h2 : u (a.1, b.2) = u b := (hfac (a.1, b.2)).trans (hfac b).symm
  exact h1.trans h2

/-- A premise aligned with the descriptor through a bijection-like map is the
sufficiency itself: S for `g ∘ k` iff S for `k`, when `g` is injective. -/
theorem aligned_premise_iff {D K V U : Type} (k : D → K) (g : K → V)
    (hg : ∀ x y, g x = g y → x = y) (u : D → U) :
    Suff (fun x => g (k x)) u ↔ Suff k u := by
  constructor
  · intro h s t hst
    exact h s t (by show g (k s) = g (k t); rw [hst])
  · intro h s t hst
    exact h s t (hg (k s) (k t) hst)

/-! ## Graphs on two vertices (copied from `PistasUnificacion.lean`) -/

def pairIndex (n : Nat) (i j : Nat) : Nat :=
  (List.range i).foldl (fun acc a => acc + (n - 1 - a)) 0 + (j - i - 1)

def edge (n bits : Nat) (i j : Fin n) : Bool :=
  if i.val < j.val then (bits >>> pairIndex n i.val j.val) % 2 == 1
  else if j.val < i.val then (bits >>> pairIndex n j.val i.val) % 2 == 1
  else false

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

/-- n = 2: connected iff universal vertex (both graphs). -/
theorem n2_equiv : (List.range 2).all (fun b => connectedB 2 b == universalB 2 b) = true := by
  decide

/-! ## The one-way coupling of F0

Unit 0 is X1 (receiver), unit 1 is X2 (driver): X1' = c X2 + ε1 with c > 0, X2' = ε2.
`par i j` means that unit `j` is a parent of unit `i` (A i j ≠ 0). -/

def par (i j : Fin 2) : Bool := i.val == 0 && j.val == 1

def undirected (i j : Fin 2) : Bool := par i j || par j i

def universalU : Bool :=
  (List.finRange 2).any (fun w => (List.finRange 2).all (fun v => v == w || undirected w v))

def bothWaysHub : Bool :=
  (List.finRange 2).any (fun w => (List.finRange 2).all (fun v => v == w || (par w v && par v w)))

/-- Undirected reading (the one formalized in `PistasUnificacion` and
`UnificacionCat`): F0 has a universal vertex. Both-directions reading: it has none. -/
theorem f0_hub_readings : universalU = true ∧ bothWaysHub = false := by
  decide

end GaussConexion

#print axioms GaussConexion.plateau_product
#print axioms GaussConexion.aligned_premise_iff
#print axioms GaussConexion.n2_equiv
#print axioms GaussConexion.f0_hub_readings
