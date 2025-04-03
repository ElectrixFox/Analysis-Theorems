import Mathlib

def bound_below (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≤ x

def bound_above (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≥ x
def bound_above_by (X : Set ℝ) (c : ℝ) : Prop := ∀ x, x ∈ X → c ≥ x

def bound_below_by (X : Set ℝ) (c : ℝ) : Prop := bound_below X → ∀ x, x ∈ X → c ≤ x

def bounded (X : Set ℝ) : Prop := bound_above X ∧ bound_below X

def supremum (X : Set ℝ) (C : ℝ) := (∀ x ∈ X, x ≤ C) ∧ (∀ B, (∀ x ∈ X, x ≤ B) → C ≤ B)

def infimum (X : Set ℝ) (C : ℝ) := (∀ x ∈ X, C ≤ x) → (∀ B, (∀ x ∈ X, B ≤ x) → C ≤ B)

axiom completeness_axiom (X : Set ℝ) [Nonempty X] : bound_above X → ∃ C, supremum X C

lemma subset_bound_bounded (X : Set ℝ) (hx : bound_above X) (Y : Set ℝ) (hy : ∀ y ∈ Y, y ∈ X) : bound_above Y := by
  obtain ⟨C, hC⟩ := hx
  use C
  tauto

lemma completeness_axiom_subset (X : Set ℝ) [Nonempty X] (hx : bound_above X) (Y : Set ℝ) [Nonempty Y] (hy : ∀ y ∈ Y, y ∈ X) : ∃ C, supremum Y C := by
  have h1 : bound_above Y := subset_bound_bounded X hx Y hy
  have := completeness_axiom Y h1
  apply this

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

def func_bound_above (X : Set ℝ) (f : ℝ → ℝ) : Prop := (∃ (c : ℝ), ∀ x ∈ X, f x ≤ c)

def func_sup (X : Set ℝ) (f : ℝ → ℝ) (C : ℝ) : Prop := func_bound_above X f ∧ (∀ B, (∀ x ∈ X, f x ≤ B) → C ≤ B)
