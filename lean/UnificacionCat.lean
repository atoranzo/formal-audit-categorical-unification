/-!
# UnificacionCat.lean — theories of consciousness as projections of one open
# dynamics: what the categorical structure proves and where it stops.

Lean 4 core (4.24.0), no Mathlib. Functors from the groupoid of open systems
(isomorphisms = relabellings preserving dynamics and blanket roles) into
discrete categories are exactly isomorphism-invariant maps; we therefore work
with maps on a type `S` of systems up to isomorphism. Nothing here establishes a
bridge law or attributes experience to any system.

* `pairing_unique` : the joint projection into the product exists and is unique
  (universal property of the product: weak unification is free).
* `nat_iff_functional` : a translation η : D₁ → D₂ with η ∘ F₁ = F₂ (a natural
  transformation between the projections, viewed as functors into discrete
  categories) exists iff F₂ is determined by F₁.
* `bridge_iff_agree` : a single phenomenal assignment through two bridge
  laws exists iff the bridge square commutes on every system.
* `reconstruction_iff_injective` : the systems are recovered from their joint
  projection iff the joint projection is injective (on isomorphism classes).
* A concrete four-unit example: ring, star, path and split systems; integration
  positivity (connected support) versus broadcast (a hub: a unit adjacent to every
  other unit in the undirected support graph).
-/

namespace UnificacionCat

attribute [local instance] Classical.propDecidable

/-- Weak unification: the pairing into the product exists and is unique. -/
theorem pairing_unique {S D₁ D₂ : Type} (F₁ : S → D₁) (F₂ : S → D₂) :
    (∀ x, ((fun x => (F₁ x, F₂ x)) x).1 = F₁ x ∧ ((fun x => (F₁ x, F₂ x)) x).2 = F₂ x) ∧
    (∀ h : S → D₁ × D₂, (∀ x, (h x).1 = F₁ x) → (∀ x, (h x).2 = F₂ x) →
      ∀ x, h x = (F₁ x, F₂ x)) := by
  refine ⟨fun x => ⟨rfl, rfl⟩, ?_⟩
  intro h h1 h2 x
  cases hx : h x with
  | mk a b =>
    have ha : a = F₁ x := by rw [← h1 x, hx]
    have hb : b = F₂ x := by rw [← h2 x, hx]
    rw [ha, hb]

/-- A translation from theory 1 to theory 2 exists iff theory 2's invariant is a
function of theory 1's (classical choice builds η; `Inhabited D₂` for values of
D₁ outside the image). -/
theorem nat_iff_functional {S D₁ D₂ : Type} [Inhabited D₂] (F₁ : S → D₁) (F₂ : S → D₂) :
    (∃ η : D₁ → D₂, ∀ x, η (F₁ x) = F₂ x) ↔ (∀ x y, F₁ x = F₁ y → F₂ x = F₂ y) := by
  constructor
  · intro ⟨η, hη⟩ x y hxy
    rw [← hη x, ← hη y, hxy]
  · intro h
    refine ⟨fun d => if hd : ∃ x, F₁ x = d then F₂ (Classical.choose hd) else default, ?_⟩
    intro x
    have hd : ∃ y, F₁ y = F₁ x := ⟨x, rfl⟩
    show (if hd : ∃ y, F₁ y = F₁ x then F₂ (Classical.choose hd) else default) = F₂ x
    rw [dif_pos hd]
    exact h _ _ (Classical.choose_spec hd)

/-- Bridge consistency: one assignment Ψ factoring through both bridges exists
iff the square G₁ ∘ F₁ = G₂ ∘ F₂ commutes. -/
theorem bridge_iff_agree {S D₁ D₂ V : Type} (F₁ : S → D₁) (F₂ : S → D₂)
    (G₁ : D₁ → V) (G₂ : D₂ → V) :
    (∃ Ψ : S → V, (∀ x, Ψ x = G₁ (F₁ x)) ∧ (∀ x, Ψ x = G₂ (F₂ x))) ↔
      (∀ x, G₁ (F₁ x) = G₂ (F₂ x)) := by
  constructor
  · intro ⟨Ψ, h1, h2⟩ x; rw [← h1 x, h2 x]
  · intro h; exact ⟨fun x => G₁ (F₁ x), fun _ => rfl, fun x => h x⟩

/-- Reconstruction: systems are recovered from the joint projection iff it is
injective; otherwise every non-injectivity witness is a blind spot. -/
theorem reconstruction_iff_injective {S D : Type} [Inhabited S] (F : S → D) :
    (∃ R : D → S, ∀ x, R (F x) = x) ↔ (∀ x y, F x = F y → x = y) := by
  constructor
  · intro ⟨R, hR⟩ x y hxy; rw [← hR x, ← hR y, hxy]
  · intro h
    refine ⟨fun d => if hd : ∃ x, F x = d then Classical.choose hd else default, ?_⟩
    intro x
    have hd : ∃ y, F y = F x := ⟨x, rfl⟩
    show (if hd : ∃ y, F y = F x then Classical.choose hd else default) = x
    rw [dif_pos hd]
    exact h _ _ (Classical.choose_spec hd)

/-! ## A concrete example on four units

Off-diagonal support of the coupling matrix A of a linear-Gaussian open system
X_{t+1} = A X_t + ε (units i and j are coupled, A_ij ≠ 0 or A_ji ≠ 0, when `adj s i j`). For the residual
integration functional J (minimum over bipartitions of
½ log det(E + (A−B)P(A−B)ᵀ)/det E over block-disconnected B), J > 0 iff the
undirected support graph is connected (proved on paper: Lemma "Gaussian
integration and connectivity", Section 3 of the paper; checked numerically by
`python/numeric/J_conectividad.py` of the archive that accompanies the paper).
Broadcast in the GNWT sense is modelled structurally by a
hub of the undirected support graph (a unit coupled, in at least one direction, to
every other unit); for the symmetric couplings of the example this is the same as
requiring coupling in both directions. -/

inductive Sys | ring | star | path | split
  deriving DecidableEq, Repr

/-- Undirected support: unordered pairs with a coupling in either direction. -/
def adj : Sys → Fin 4 → Fin 4 → Bool
  | .ring,  i, j => (i.val + 1) % 4 == j.val || (j.val + 1) % 4 == i.val
  | .star,  i, j => i ≠ j && (i.val == 0 || j.val == 0)
  | .path,  i, j => i.val + 1 == j.val || j.val + 1 == i.val
  | .split, i, j => (i.val / 2 == j.val / 2) && i ≠ j

/-- Reachability in at most three steps (enough on four vertices). -/
def reach (s : Sys) (i j : Fin 4) : Bool :=
  i == j || adj s i j ||
  (List.finRange 4).any (fun k => adj s i k && adj s k j) ||
  (List.finRange 4).any (fun k => (List.finRange 4).any (fun l => adj s i k && adj s k l && adj s l j))

/-- Integration positivity of the Gaussian functional: connected support. -/
def Ipos (s : Sys) : Bool := (List.finRange 4).all (fun i => (List.finRange 4).all (fun j => reach s i j))

/-- Broadcast: some unit is adjacent to every other unit in the undirected support. -/
def Bcast (s : Sys) : Bool :=
  (List.finRange 4).any (fun w => (List.finRange 4).all (fun v => v == w || adj s w v))

/-- Free-energy projection as a bare blanket predicate: every object of the base
category carries a Markov blanket, so the predicate is constant. -/
def Blanket (_ : Sys) : Bool := true

theorem values :
    (Ipos .ring, Bcast .ring) = (true, false) ∧ (Ipos .star, Bcast .star) = (true, true) ∧
    (Ipos .path, Bcast .path) = (true, false) ∧ (Ipos .split, Bcast .split) = (false, false) := by
  decide

/-- The IIT-type and GNWT-type presence squares do not commute: they disagree on
the ring (and on the path). -/
theorem square_fails : ∃ s : Sys, Ipos s ≠ Bcast s := ⟨.ring, by decide⟩

/-- No translation from integration positivity to broadcast exists. -/
theorem no_translation : ¬ ∃ η : Bool → Bool, ∀ s : Sys, η (Ipos s) = Bcast s := by
  intro ⟨η, h⟩
  have h1 := h .ring
  have h2 := h .star
  have e1 : Ipos .ring = true := by decide
  have e2 : Ipos .star = true := by decide
  have b1 : Bcast .ring = false := by decide
  have b2 : Bcast .star = true := by decide
  rw [e1, b1] at h1; rw [e2, b2] at h2
  rw [h1] at h2; exact Bool.noConfusion h2

/-- On the subdomain {star, split} the squares commute: a unified presence
assignment exists there. -/
theorem square_commutes_on_sub : ∀ s : Sys, (s = .star ∨ s = .split) → Ipos s = Bcast s := by
  intro s hs; rcases hs with h | h <;> subst h <;> decide

/-- Blind spot: ring and path have the same joint projection (integration
positivity, broadcast, blanket) but are not isomorphic (degree sequences differ). -/
def degree (s : Sys) (i : Fin 4) : Nat := ((List.finRange 4).filter (fun j => adj s i j)).length
theorem blind_spot :
    (Ipos .ring, Bcast .ring, Blanket .ring) = (Ipos .path, Bcast .path, Blanket .path) ∧
    (List.finRange 4).map (degree .ring) ≠ (List.finRange 4).map (degree .path) := by
  decide

/-- Insertion sort on natural numbers (no Mathlib), to compare degree multisets. -/
def insertSorted : Nat → List Nat → List Nat
  | x, [] => [x]
  | x, y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def sortNat : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (sortNat xs)

/-- The degree multisets of ring and path differ ({2,2,2,2} versus {1,1,2,2}). The
degree multiset is an isomorphism invariant (standard; not formalized here), so ring
and path are not isomorphic although their joint presence projection agrees. -/
theorem blind_spot_multiset :
    sortNat ((List.finRange 4).map (degree .ring)) = [2, 2, 2, 2] ∧
    sortNat ((List.finRange 4).map (degree .path)) = [1, 1, 2, 2] := by
  decide

/-- The blanket projection agrees with broadcast only where broadcast holds. -/
theorem blanket_vs_broadcast : Blanket .ring ≠ Bcast .ring := by decide

end UnificacionCat

#print axioms UnificacionCat.pairing_unique
#print axioms UnificacionCat.nat_iff_functional
#print axioms UnificacionCat.bridge_iff_agree
#print axioms UnificacionCat.reconstruction_iff_injective
#print axioms UnificacionCat.values
#print axioms UnificacionCat.square_fails
#print axioms UnificacionCat.no_translation
#print axioms UnificacionCat.square_commutes_on_sub
#print axioms UnificacionCat.blind_spot
#print axioms UnificacionCat.blind_spot_multiset
#print axioms UnificacionCat.blanket_vs_broadcast
