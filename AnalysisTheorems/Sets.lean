import Mathlib

def bound_above (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≥ x
def bound_below (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≤ x

def bound_above' (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≥ x
def bound_above_by' (X : Set ℝ) (c : ℝ) : Prop := ∀ x, x ∈ X → c ≥ x

def bound_above_by (X : Set ℝ) (c : ℝ) : Prop := bound_above X → ∀ x, x ∈ X → x ≤ c
def bound_below_by (X : Set ℝ) (c : ℝ) : Prop := bound_below X → ∀ x, x ∈ X → c ≤ x

def supremum (X : Set ℝ) (C : ℝ) := bound_above_by X C → (∀ (B : ℝ), (bound_above_by X B) → (C ≤ B))
def supremum' (X : Set ℝ) (C : ℝ) := (∀ x ∈ X, x ≤ C) ∧ (∀ B, (∀ x ∈ X, x ≤ B) → C ≤ B)

def infimum (X : Set ℝ) := bound_below X → ∃ (C : ℝ), ∀ (B : ℝ), (bound_below_by X C) ∧ (bound_below_by X B) ∧ (C ≤ B)

example (X : Set ℝ) (hX : X = {x : ℝ | x < 2}) : bound_above_by X 2 := by
  intro h x hx
  generalize hc : (2 : ℝ) = c
  rw [hX] at hx
  rw [Set.mem_setOf] at hx
  linarith

example (X : Set ℝ) (hX : X = {x : ℝ | x < 2}) : supremum X 2 := by
  intro hb B
  by_contra h1
  simp at h1
  obtain ⟨h2, h3⟩ := h1
  have h5 : bound_above X := by
    dsimp[bound_above_by] at hb
    use 2
    intro x hx
    rw [hX] at hx
    simp at hx
    linarith

  specialize hb

  have h4 : B < 2 := by
    calc
      B = (B + B) / 2 := by simp
      _ < (B + 2) / 2 := by linarith
      _ < (2 + 2) / 2 := by linarith
      _ = 2 := by simp
  subst X
  dsimp [bound_above] at h5
  obtain ⟨c, hc⟩ := h5
  specialize hc B
  simp at hc
  simp_all only [imp_self, true_implies]
  
example (X : Set ℝ) (hX : X = {x : ℝ | x < 2}) : supremum' X 2 := by
  rw [hX]
  constructor
  . 
    intro x hx
    exact le_of_lt hx
  . 
    intro B hB
    apply le_of_not_lt
    intro hbl
    let x := (B + 2) / 2
    have hxin : x ∈ {x : ℝ | x < 2} := by
      subst hX
      simp
      calc
        x = (B + 2) / 2 := by rfl
        _ < (2 + 2) / 2 := by linarith
        _ = 2 := by norm_num
    have : x ≤ B := hB x hxin
    simp at hxin
    specialize hB x
    simp at hB
    contrapose hB
    simp at hB
    simp
    constructor
    linarith
    simp [x]
    linarith

example (X : Set ℝ) (hX : X = {x : ℝ | x < 2}) : supremum' X 2 := by
  intro hb B
  by_contra h1
  simp at h1
  obtain ⟨h2, h3⟩ := h1
  have h5 : bound_above' X := by
    dsimp[bound_above_by'] at hb
    use 2
    /-
    intro x hx
    rw [hX] at hx
    simp at hx
    linarith
    -/

  specialize hb

  have h4 : B < 2 := by
    calc
      B = (B + B) / 2 := by simp
      _ < (B + 2) / 2 := by linarith
      _ < (2 + 2) / 2 := by linarith
      _ = 2 := by simp
  subst X
  dsimp [bound_above'] at h5
  obtain ⟨c, hc⟩ := h5
  specialize hc B
  simp at hc
  simp_all only [imp_self, true_implies]
  
