import Mathlib

def bound_above (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≥ x
def bound_below (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≤ x

def bound_above_by (X : Set ℝ) (c : ℝ) : Prop := bound_above X → ∀ x, x ∈ X → x ≤ c
def bound_below_by (X : Set ℝ) (c : ℝ) : Prop := bound_below X → ∀ x, x ∈ X → c ≤ x

def supremum (X : Set ℝ) (C : ℝ) := bound_above_by X C → (∀ (B : ℝ), (bound_above_by X B) → (C ≤ B))

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
  
