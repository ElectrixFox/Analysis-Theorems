import Mathlib

-- def bound_above (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≥ x
def bound_below (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≤ x

def bound_above (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≥ x
def bound_above_by (X : Set ℝ) (c : ℝ) : Prop := ∀ x, x ∈ X → c ≥ x

-- def bound_above_by (X : Set ℝ) (c : ℝ) : Prop := bound_above X → ∀ x, x ∈ X → x ≤ c
def bound_below_by (X : Set ℝ) (c : ℝ) : Prop := bound_below X → ∀ x, x ∈ X → c ≤ x

-- def supremum (X : Set ℝ) (C : ℝ) := bound_above_by X C → (∀ (B : ℝ), (bound_above_by X B) → (C ≤ B))
def supremum (X : Set ℝ) (C : ℝ) := (∀ x ∈ X, x ≤ C) ∧ (∀ B, (∀ x ∈ X, x ≤ B) → C ≤ B)

def supremum' (X : Set ℝ) (C : ℝ) := bound_above_by X C ∧ (∀ B, (bound_above_by X B) → C ≤ B)


def infimum (X : Set ℝ) := bound_below X → ∃ (C : ℝ), ∀ (B : ℝ), (bound_below_by X C) ∧ (bound_below_by X B) ∧ (C ≤ B)

example (X : Set ℝ) (hX : X = {x : ℝ | x < 2}) : bound_above_by X 2 := by
  intro x hx
  generalize hc : (2 : ℝ) = c
  rw [hX] at hx
  rw [Set.mem_setOf] at hx
  linarith

example (X : Set ℝ) (hX : X = {x : ℝ | x < 2}) : supremum X 2 := by
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

  /-
  have h4 : B < 2 := by
    calc
      B = (B + B) / 2 := by simp
      _ < (B + 2) / 2 := by linarith
      _ < (2 + 2) / 2 := by linarith
      _ = 2 := by simp
  -/
  
theorem archimedes (a b : ℝ) (hb : b > 0) : ∃ (n : ℕ), n * b > a := by
  by_contra h
  simp at h
  let X : Set ℝ := {n * b | n : ℕ}
  have hXb : bound_above_by X a := by sorry
  have hXsup : ∃ C, supremum X C := by sorry
  obtain ⟨C, hC⟩ := hXsup

  have hnup : ¬(bound_above_by X (C - b)) := by sorry
  
  dsimp [bound_above_by] at hnup
  simp at hnup
  
  obtain ⟨x, hx, h2⟩ := hnup
  apply lt_add_of_sub_left_lt at h2
  have : b + x ∈ X := by
    dsimp [X] at hx
    obtain ⟨n, hn⟩ := hx
    rw [←hn]
    dsimp [X]
    use n + 1
    norm_num
    rw [mul_comm, mul_add]
    simp [add_comm]
    rw [mul_comm]

axiom completeness_axiom {X : Set ℝ} [Nonempty X] : bound_above X → ∃ C, supremum X C

theorem archimedes' (a b : ℝ) (hb : b > 0) : ∃ (n : ℕ), n * b > a := by
  by_contra h
  simp at h
  let X : Set ℝ := {n * b | n : ℕ}  -- define the set
  have hXn : Nonempty X := by -- nonempty
    simp  -- simplify to there is an a in X
    use b -- b is naturally in X
    dsimp [X]
    use 1 -- 1 * b = b
    simp  -- simplification

  have hXb : bound_above X := by  -- it is obviously bounded above by a
    use a
    simp
    dsimp [X]
    intro x hx
    obtain ⟨n, hn⟩ := hx
    subst hn
    apply h

  have hXsup : ∃ C, supremum X C := completeness_axiom hXb  -- by the completeness axiom it has a supremum
  obtain ⟨C, hC⟩ := hXsup
  clear hXb
  have hnup : ¬(bound_above_by X (C - b)) := by sorry


  
  have hnmp : ∃ (n : ℕ), n * b > C - b := by sorry
  obtain ⟨n, hn⟩ := hnmp

  have : (n + 1) * b > C := by sorry
  dsimp [supremum] at hC
  obtain ⟨h1, h2⟩ := hC
  specialize h1 (b * (n + 1))
  
  
  dsimp [bound_above_by] at hnup
  simp at hnup
  
  obtain ⟨x, hx, h2⟩ := hnup
  apply lt_add_of_sub_left_lt at h2
  have : b + x ∈ X := by
    dsimp [X] at hx
    obtain ⟨n, hn⟩ := hx
    rw [←hn]
    dsimp [X]
    use n + 1
    norm_num
    rw [mul_comm, mul_add]
    simp [add_comm]
    rw [mul_comm]
