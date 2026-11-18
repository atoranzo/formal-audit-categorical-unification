/-!
# FiltracionCociente.lean — Lines 1-4 of Section 4 of the paper: filtration,
# quotient by the factorizable ideal, variational selection and the weak limit,
# with what each can and cannot deliver. Lean 4 core (4.24.0), no Mathlib.
# Combinatorial and logical parts only; analytic bounds on J are proved on paper.
-/

namespace FiltracionCociente

/-! ## Line 1: filtration Central ⊆ Connected ⊆ All and the exact non-commutation locus -/

/-- If broadcast implies connectivity (`hsub`), the presence squares disagree exactly
on the band "connected and without a broadcast vertex". -/
theorem noncomm_locus {S : Type} (Central Conn : S → Bool)
    (hsub : ∀ x, Central x = true → Conn x = true) :
    ∀ x, Conn x ≠ Central x ↔ (Conn x = true ∧ Central x = false) := by
  intro x
  cases hc : Central x <;> cases hk : Conn x
  · simp
  · simp
  · have := hsub x hc; rw [hk] at this; exact absurd this (by simp)
  · simp

/-- On the bottom and top levels of the filtration the squares commute. -/
theorem commute_off_band {S : Type} (Central Conn : S → Bool)
    (hsub : ∀ x, Central x = true → Conn x = true) (x : S)
    (h : Central x = true ∨ Conn x = false) : Conn x = Central x := by
  rcases h with h | h
  · rw [h, hsub x h]
  · cases hc : Central x
    · rw [h]
    · have := hsub x hc; rw [h] at this; exact absurd this (by simp)

/-! ## Line 2: zero-product monoid and the collapse of the factorizable ideal -/

/-- A value type with an adjoined unit; products of two non-unit values collapse to `z`. -/
def zmul {D : Type} (z : D) : Option D → Option D → Option D
  | none, b => b
  | a, none => a
  | some _, some _ => some z

theorem zmul_assoc {D : Type} (z : D) (a b c : Option D) :
    zmul z (zmul z a b) c = zmul z a (zmul z b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem zmul_unit_left {D : Type} (z : D) (a : Option D) : zmul z none a = a := by
  cases a <;> rfl

theorem zmul_unit_right {D : Type} (z : D) (a : Option D) : zmul z a none = a := by
  cases a <;> rfl

/-- Abstract monoidal objects: a tensor, a unit and "nonempty". If a projection is
`z` on every tensor of two nonempty objects and sends the unit to the adjoined unit,
it is strong monoidal into the zero-product monoid. -/
theorem strong_monoidal_zero {S D : Type} (tensor : S → S → S) (unit : S)
    (nonempty : S → Prop) (F : S → Option D) (z : D)
    (hunitL : ∀ x, tensor unit x = x) (hunitR : ∀ x, tensor x unit = x)
    (hne : ∀ x, x ≠ unit → nonempty x) (hF0 : F unit = none)
    (hFne : ∀ x, nonempty x → ∃ d, F x = some d)
    (hvan : ∀ x y, nonempty x → nonempty y → F (tensor x y) = some z) :
    ∀ x y, F (tensor x y) = zmul z (F x) (F y) := by
  intro x y
  by_cases hx : x = unit
  · subst hx; rw [hunitL, hF0, zmul_unit_left]
  by_cases hy : y = unit
  · subst hy; rw [hunitR, hF0, zmul_unit_right]
  obtain ⟨dx, hdx⟩ := hFne x (hne x hx)
  obtain ⟨dy, hdy⟩ := hFne y (hne y hy)
  rw [hvan x y (hne x hx) (hne y hy), hdx, hdy]; rfl

/-- Collapse of an ideal `I` of objects to a single point: a projection factors through
the collapse iff it is constant on `I`. -/
theorem factors_through_collapse {S D : Type} (I : S → Bool) (F : S → D) (b : D) :
    (∃ G : Option S → D, G none = b ∧ ∀ x, F x = G (if I x then none else some x)) ↔
      (∀ x, I x = true → F x = b) := by
  constructor
  · intro ⟨G, hG0, hG⟩ x hx
    rw [hG x, hx, if_pos rfl, hG0]
  · intro h
    refine ⟨fun o => match o with | none => b | some x => F x, rfl, ?_⟩
    intro x
    cases hx : I x
    · simp
    · simp; exact h x hx

/-! ## Line 3: variational selection does not give S_u -/

def Suff {D V U : Type} (Φ : D → V) (u : D → U) : Prop := ∀ s t, Φ s = Φ t → u s = u t

/-- Restricting the domain to the image of a section makes every fibre a singleton, so
S_u becomes vacuously true for every u: the obligation is not met, it is removed. -/
theorem restriction_vacuous {D V U : Type} (Φ : D → V) (sec : V → D) (u : D → U) :
    Suff (fun x : {x : D // x = sec (Φ x)} => Φ x.1) (fun x => u x.1) := by
  intro ⟨s, hs⟩ ⟨t, ht⟩ h
  simp only at h ⊢
  rw [hs, ht, h]

/-- SEG, written for the representation ψ ∘ 𝔘, is S_u for that degree: requiring it to
collapse a fibre is circular. -/
theorem seg_is_Su {D V H U : Type} (Φ : D → V) (𝔘 : D → H) (ψ : H → U) :
    (∀ s t, Φ s = Φ t → ψ (𝔘 s) = ψ (𝔘 t)) ↔ Suff Φ (fun s => ψ (𝔘 s)) := Iff.rfl

/-- SEG as a grouping of the coexperience structures present: `g` assigns a group to
each structure, ψ is constant on each group, there are at least two groups, and no
Φ-value hosts two groups. -/
def SEG {D V H U G : Type} (Φ : D → V) (𝔘 : D → H) (ψ : H → U) (g : H → G) : Prop :=
  (∀ s t, g (𝔘 s) = g (𝔘 t) → ψ (𝔘 s) = ψ (𝔘 t)) ∧
  (∃ s t, g (𝔘 s) ≠ g (𝔘 t)) ∧
  (∀ s t, Φ s = Φ t → g (𝔘 s) = g (𝔘 t))

/-- SEG implies S_u for u = ψ ∘ 𝔘. -/
theorem seg_implies_Su {D V H U G : Type} (Φ : D → V) (𝔘 : D → H) (ψ : H → U) (g : H → G)
    (h : SEG Φ 𝔘 ψ g) : Suff Φ (fun s => ψ (𝔘 s)) :=
  fun s t hst => h.1 s t (h.2.2 s t hst)

/-- SEG with ψ distinct between distinct groups. -/
def SEGd {D V H U G : Type} (Φ : D → V) (𝔘 : D → H) (ψ : H → U) (g : H → G) : Prop :=
  SEG Φ 𝔘 ψ g ∧ ∀ s t, ψ (𝔘 s) = ψ (𝔘 t) → g (𝔘 s) = g (𝔘 t)

/-- Exact form: some grouping satisfies SEG with ψ distinct between groups iff S_u holds
and the degree ψ ∘ 𝔘 is not constant. SEG is S_u (non-degenerate) restated. -/
theorem segd_iff {D V H U : Type} (Φ : D → V) (𝔘 : D → H) (ψ : H → U) :
    (∃ (G : Type) (g : H → G), SEGd Φ 𝔘 ψ g) ↔
      (Suff Φ (fun s => ψ (𝔘 s)) ∧ ∃ s t, ψ (𝔘 s) ≠ ψ (𝔘 t)) := by
  constructor
  · intro ⟨G, g, hseg, hdist⟩
    refine ⟨seg_implies_Su Φ 𝔘 ψ g hseg, ?_⟩
    obtain ⟨s, t, hne⟩ := hseg.2.1
    exact ⟨s, t, fun he => hne (hdist s t he)⟩
  · intro ⟨hS, s, t, hne⟩
    exact ⟨U, ψ, ⟨⟨fun _ _ h => h, ⟨s, t, hne⟩, hS⟩, fun _ _ h => h⟩⟩

/-! ## Line 4: the weak limit (pullback) of the section and the descriptor -/

/-- The pullback of a section `sec : V → D` along Φ is the set of canonical representatives;
on it the joint projection (Φ, w) is a function of Φ alone, so no information is added
beyond the section. -/
theorem pullback_determined {D V W : Type} (Φ : D → V) (w : D → W) (sec : V → D) :
    ∀ x : {x : D // x = sec (Φ x)}, w x.1 = w (sec (Φ x.1)) := by
  intro ⟨x, hx⟩
  simp only
  rw [← hx]

end FiltracionCociente

#print axioms FiltracionCociente.noncomm_locus
#print axioms FiltracionCociente.commute_off_band
#print axioms FiltracionCociente.zmul_assoc
#print axioms FiltracionCociente.strong_monoidal_zero
#print axioms FiltracionCociente.factors_through_collapse
#print axioms FiltracionCociente.restriction_vacuous
#print axioms FiltracionCociente.seg_implies_Su
#print axioms FiltracionCociente.segd_iff
#print axioms FiltracionCociente.seg_is_Su
#print axioms FiltracionCociente.pullback_determined
