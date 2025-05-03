import Mathlib

def bound_below (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≤ x
def bound_below_by (X : Set ℝ) (c : ℝ) : Prop := ∀ x, x ∈ X → c ≤ x

def bound_above (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≥ x
def bound_above_by (X : Set ℝ) (c : ℝ) : Prop := ∀ x, x ∈ X → c ≥ x

def bounded (X : Set ℝ) : Prop := bound_above X ∧ bound_below X

/- For X ⊆ ℝ the maximum is an element in X such that ∀ x ∈ X, x ≤ M -/
def maximum (X : Set ℝ) (M : ℝ) : Prop := M ∈ X ∧ ∀ x ∈ X, x ≤ M

/- For X ⊆ ℝ the minimum is an element in X such that ∀ x ∈ X, m ≤ x -/
def minimum (X : Set ℝ) (m : ℝ) : Prop := m ∈ X ∧ ∀ x ∈ X, m ≤ x

def supremum (X : Set ℝ) (C : ℝ) := (∀ x ∈ X, x ≤ C) ∧ (∀ B, (∀ x ∈ X, x ≤ B) → C ≤ B)

def infimum (X : Set ℝ) (C : ℝ) := (∀ x ∈ X, C ≤ x) ∧ (∀ B, (∀ x ∈ X, B ≤ x) → C ≤ B)


lemma lt_add_imp_le (a b : ℝ) : (∀ ε > 0, a < b + ε) → a ≤ b := by
  intro h
  by_contra h1  -- assume a > b
  push_neg at h1
  rw [show b < a ↔ b - a < 0 by simp] at h1 -- show b - a < 0
  specialize h (a - b)  -- so use ε = a - b
  simp at h -- then this says b < a and a ≤ b which is clearly a contradiction
  linarith

lemma abs_sub_le_add (a b c : ℝ) : |a - b| < c → |a| ≤ |b| + c := by
  intro h
  have h1 := calc
      |a| = |a - b + b| := by simp
      _ ≤ |a - b| + |b| := by apply abs_add
  linarith

lemma abs_le_imp_le (a b : ℝ) : |a| ≤ b → a ≤ b := by
  intro h
  by_cases h1 : a ≤ 0
  .
    rw [abs_of_nonpos h1] at h
    linarith
  .
    push_neg at h1
    rw [abs_of_pos h1] at h
    exact h

axiom completeness_axiom (X : Set ℝ) [Nonempty X] : bound_above X → ∃ C, supremum X C

lemma subset_bound_bounded (X : Set ℝ) (hx : bound_above X) (Y : Set ℝ) (hy : ∀ y ∈ Y, y ∈ X) : bound_above Y := by
  obtain ⟨C, hC⟩ := hx
  use C
  tauto

lemma completeness_axiom_subset (X : Set ℝ) [Nonempty X] (hx : bound_above X) (Y : Set ℝ) [Nonempty Y] (hy : ∀ y ∈ Y, y ∈ X) : ∃ C, supremum Y C :=
  completeness_axiom Y (subset_bound_bounded X hx Y hy)

theorem archimedes (a b : ℝ) (hb : b > 0) : ∃ (n : ℕ), n * b > a := by
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

  have hXsup : ∃ C, supremum X C := completeness_axiom X hXb  -- by the completeness axiom it has a supremum
  obtain ⟨C, hC⟩ := hXsup -- get the supremum
  clear hXb hXn -- clean up some unnecessary hypothesis
  have hBup : (bound_above_by X C) := hC.left
  have hnup : ¬(bound_above_by X (C - b)) := by
    by_contra h -- assume it is an upper bound
    dsimp [supremum] at hC  -- break up the supremum
    rw [←bound_above_by] at hC  -- the supremum says that X is bounded above by C
    obtain ⟨h1, h2⟩ := hC
    specialize h2 (C - b) -- the new supremum is C - b
    rw [←bound_above_by] at h2  -- this means X is bounded above by C - b implies C ≤ C - b
    apply h2 at h
    linarith  -- obviously this is false

  have : ∃ (n : ℕ), n * b > C - b := by
    dsimp [bound_above_by] at hnup
    simp at hnup -- sort out the not
    obtain ⟨x, hx1, hx2⟩ := hnup  -- get the hypothesis for being bounded above
    dsimp [X] at hx1
    obtain ⟨n, hn⟩ := hx1 -- get our needed n
    rw [←hn] at hx2 -- rewrite the definition of x
    use n -- with this n we have the goal


  obtain ⟨n, hn⟩ := this  -- get our n
  have hnxtinX : (n + 1) * b ∈ X := by  -- show that (n + 1) * b is in X
    use (n + 1)
    simp

  specialize hBup ((n + 1) * b) -- this (n + 1) * b is our needed element for the contradiction
  apply hBup at hnxtinX -- apply the contradition
  linarith  -- hence contradiction

lemma set_bound_above_neg_bound_below (X : Set ℝ) : bound_above X ↔ bound_below (-X) := by
  constructor
  repeat' -- repeat this as the following works in both ways
  . intro h
    obtain ⟨c, hc⟩ := h -- get the upper (lower) bound
    use (-c)  -- the lower (upper) bound is -c since c is positive
    intro x
    specialize hc (-x)  -- the x in X will be -x since x is -ve
    simp_all [neg_le, le_neg] -- cleaning up the inequalities

lemma inf_of_neg_eq_neg_sup' (X : Set ℝ) [Nonempty X] (hX : bound_above X)
  : infimum (-X) ((-1) * (completeness_axiom X hX).choose) := by

  set sup := (completeness_axiom X hX).choose
  simp
  constructor
  .
    sorry
  .
    intro x hx
    simp at hx
    unfold bound_above at hX
    obtain ⟨c, hc⟩ := hX
    specialize hc (-x)
    sorry

lemma inf_of_neg_eq_neg_sup (X : Set ℝ) [Nonempty X] (hX : bound_above X) :
  ∃ C, (supremum X (-C) ↔ infimum (-X) C) := by
  have h := completeness_axiom X hX
  obtain ⟨C, hC⟩ := h
  use (-C)
  simp [hC]
  set T := -X
  have h0 : ∀ x ∈ T, -C ≤ x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hC
    specialize h1 (-x)
    apply h1 at hx
    rw [neg_le]
    exact hx
  constructor
  exact h0
  intro B

  by_cases h : ¬∃ ε > 0, ∀ x ∈ T, B + ε ≤ x
  .
    push_neg at h
    intro h1
    apply lt_add_imp_le
    intro ε hε
    specialize h ε hε
    obtain ⟨x, hx, hx1⟩ := h
    specialize h1 x hx
    specialize h0 x hx
    calc
      -C ≤ x := h0
      _ < B + ε := hx1
  .
    push_neg at h
    obtain ⟨ε, hε, h⟩ := h
    intro h1
    conv at h1 =>
      intro x hx
      rw [←neg_le_neg_iff]


    have h2 : ∀ x ∈ X, x ≤ -B := by
      intro x hx
      specialize h1 (-x)
      simp [T, hx] at h1
      exact h1

    have h3 : C ≥ -B := by
      sorry

    have h4 : C ≤ -B := (hC.right (-B)) h2

    dsimp [supremum] at hC
    obtain ⟨h3, h4⟩ := hC
    specialize h4 (-B)
    apply h4 at h2
    rw [le_neg] at h2
    simp [T] at *
    sorry


  /-have h := completeness_axiom X hX
  obtain ⟨C, hC⟩ := h
  use (-C)
  simp [hC]
  constructor
  .
    rw [show (∀ x ∈ -X, -C ≤ x) ↔ bound_below (-X) by
      unfold bound_below
      constructor
      intro h
      use (-C)
      intro h x hx
      unfold supremum at hC
      simp at hx
      rw [neg_le]
      apply hC.left (-x) hx
      ]
    rw [set_bound_above_neg_bound_below] at hX
    exact hX
  .
    contrapose hC
    unfold supremum
    simp
    intro h
    push_neg at hC
    obtain ⟨B, ⟨h1, h2⟩⟩ := hC
    use B
    constructor
    intro x hx
    specialize h1 (-x)
    simp at h1
    specialize h (-x)
    sorry-/

def func_bound_above (X : Set ℝ) (f : ℝ → ℝ) : Prop := (∃ (c : ℝ), ∀ x ∈ X, f x ≤ c)

def func_sup (X : Set ℝ) (f : ℝ → ℝ) (C : ℝ) : Prop := func_bound_above X f ∧ (∀ B, (∀ x ∈ X, f x ≤ B) → C ≤ B)
