import Mathlib

def bound_below (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≤ x

def bound_above (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≥ x
def bound_above_by (X : Set ℝ) (c : ℝ) : Prop := ∀ x, x ∈ X → c ≥ x

def bound_below_by (X : Set ℝ) (c : ℝ) : Prop := bound_below X → ∀ x, x ∈ X → c ≤ x

def bounded (X : Set ℝ) : Prop := bound_above X ∧ bound_below X

/- For X ⊆ ℝ the maximum is an element in X such that ∀ x ∈ X, x ≤ M -/
def maximum (X : Set ℝ) (M : ℝ) : Prop := M ∈ X ∧ ∀ x ∈ X, x ≤ M

/- For X ⊆ ℝ the minimum is an element in X such that ∀ x ∈ X, m ≤ x -/
def minimum (X : Set ℝ) (m : ℝ) : Prop := m ∈ X ∧ ∀ x ∈ X, m ≤ x

def supremum (X : Set ℝ) (C : ℝ) := (∀ x ∈ X, x ≤ C) ∧ (∀ B, (∀ x ∈ X, x ≤ B) → C ≤ B)

def infimum (X : Set ℝ) (C : ℝ) := (∀ x ∈ X, C ≤ x) ∧ (∀ B, (∀ x ∈ X, B ≤ x) → C ≤ B)

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

lemma inf_of_neg_eq_neg_sup (X : Set ℝ) (c : ℝ) [Nonempty X] (hX : bound_above X) (hS : supremum X (-c)) : infimum (-X) c := by
  unfold infimum

  -- -X is clearly bounded below
  have hBb : bound_below (-X) := by
    rw [←set_bound_above_neg_bound_below]
    exact hX

  constructor
  .
    sorry
  .
    simp
    sorry

def func_bound_above (X : Set ℝ) (f : ℝ → ℝ) : Prop := (∃ (c : ℝ), ∀ x ∈ X, f x ≤ c)

def func_sup (X : Set ℝ) (f : ℝ → ℝ) (C : ℝ) : Prop := func_bound_above X f ∧ (∀ B, (∀ x ∈ X, f x ≤ B) → C ≤ B)
