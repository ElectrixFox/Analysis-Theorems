import Mathlib

def bound_above (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≥ x
def bound_below (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≤ x

def bound_above_by (X : Set ℝ) (c : ℝ) : Prop := bound_above X → ∀ x, x ∈ X → c ≥ x
def bound_below_by (X : Set ℝ) (c : ℝ) : Prop := bound_below X → ∀ x, x ∈ X → c ≤ x

def supremum (X : Set ℝ) (C : ℝ) := bound_above_by X C → (∀ (B : ℝ), (bound_above_by X B) → (C ≤ B))

def infimum (X : Set ℝ) := bound_below X → ∃ (C : ℝ), ∀ (B : ℝ), (bound_below_by X C) ∧ (bound_below_by X B) ∧ (C ≤ B)

example (X : Set ℝ := {x : ℝ | x < 2}) : bound_above_by X 2 := by
  /-contrapose!
  simp
  intro x h1 h2
  intro h3
  dsimp [bound_above] at h3
  obtain ⟨a, ha⟩ := h3
  specialize ha x
  apply ha at h1
  simp at h1
  rw [Set.mem_setOf]
  -/
  have h3 : ∀ x, x ∈ X → x < 2 := by
    intro a ha
    let f := fun (x : ℝ) => x < 2
    -- rw [Set.mem_setOf a f] at ha


  intro hx x
  dsimp [bound_above] at hx
  obtain ⟨v, hv⟩ := hx
  specialize hv x
  rw [Set.mem_def] at hv
  intro h
  apply hv at h
  simp

  by_contra h2
  simp at h2

  simp_all

  revert h

  simp
  sorry


example (X : Set ℝ := {x : ℝ | x < 2}) : supremum X 2 := by
  intro hb B
  by_contra h1
  simp at h1
  obtain ⟨h2, h3⟩ := h1
  have h5 : bound_above X := by
    dsimp[bound_above_by] at hb
    simp at hb
    dsimp [bound_above]
    simp
    use 2
    intro a ha
    sorry

  specialize hb

  have h4 : B < 2 := by
    calc
      B = (B + B) / 2 := by simp
      _ < (B + 2) / 2 := by linarith
      _ < (2 + 2) / 2 := by linarith
      _ = 2 := by simp

  sorry
