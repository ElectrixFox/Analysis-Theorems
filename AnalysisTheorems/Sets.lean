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
axiom completeness_axiom_below (X : Set ℝ) [Nonempty X] : bound_below X → ∃ C, infimum X C

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

lemma eq_iff_le_tric (a b : ℝ) : a ≤ b ∧ b ≤ a → a = b := by
  norm_num
  intro h1 h2
  by_contra h
  push_neg at h
  rw [le_iff_eq_or_lt] at *
  obtain h1 | h1 := h1
  . exact h h1
  obtain h2 | h2 := h2
  . exact h h2.symm
  . linarith

lemma eq_iff_le_tric' (a b : ℝ) : a = b → a ≤ b → b ≤ a := by simp_all

lemma neg_set_le_bound (X : Set ℝ) (C : ℝ) : (∀ x ∈ -X, x ≤ C) ↔ (∀ x ∈ X, -x ≤ C) := by
  simp_all
  constructor
  . intro h x hx
    specialize h (-x)
    apply h
    simp [hx]
  . intro h x hx
    specialize h (-x)
    simp at h
    exact h hx

lemma neg_set_ge_bound (X : Set ℝ) (C : ℝ) : (∀ x ∈ -X, x ≥ C) ↔ (∀ x ∈ X, -x ≥ C) := by
  simp_all
  constructor
  . intro h x hx
    specialize h (-x)
    apply h
    simp [hx]
  . intro h x hx
    specialize h (-x)
    simp at h
    exact h hx


lemma inf_of_neg_eq_neg_sup' (X : Set ℝ) (hX : bound_above X) (C : ℝ) (h : supremum X (-C)) :
  supremum X (-C) ↔ infimum (-X) C := by
  simp [h]
  rename' C => p
  rw [←neg_neg p]
  set B := -p
  rename' X => S
  let T := -S
  have h1 : ∀ x ∈ S, -x ≥ -B := by
    intro x hx
    rw [ge_iff_le, neg_le_neg_iff]
    apply h.left x hx
  have h2 : ∀ t ∈ T, -B ≤ t := by
    simp [T, B, h1]
    intro t ht
    specialize h1 (-t)
    simp [ht, B] at h1
    exact h1

  constructor
  . intro s hs
    specialize h1 (-s)
    simp at hs
    simp at h1
    exact h1 hs
  .
    intro C hC
    rw [eq_iff_le_tric C (-B)]
    constructor
    .
      unfold T at h2
      obtain ⟨h3, h4⟩ := h
      simp at h1
      specialize h4 (-C)
      rw [le_neg]
      apply h4
      intro s hs
      specialize hC (-s)
      simp [le_neg] at hC
      exact hC hs
    .
      unfold T at h2
      obtain ⟨h3, h4⟩ := h
      simp at h1
      specialize h4 (-C)
      rw [neg_le]
      rw [neg_set_ge_bound] at hC
      conv at hC =>
        intro x hx
        rw [ge_iff_le, le_neg]
      rw [neg_set_ge_bound] at h2
      simp at h2
      simp_all
      sorry

lemma inf_of_neg_eq_neg_sup (X : Set ℝ) [Nonempty X] (hX : bound_above X) (C : ℝ) (hS : supremum X (-C)) :
  infimum (-X) C := by

  have : Nonempty (↑(-X)) := by
    rename_i i
    obtain ⟨a, ha⟩ := i
    use -a
    simp [ha]


  rw [set_bound_above_neg_bound_below X] at hX
  constructor
  .
    obtain ⟨h1, h2⟩ := hS
    rw [neg_set_ge_bound]
    simp [le_neg]
    exact h1
  .
    intro B hB
    obtain ⟨c, hc⟩ := hX

    obtain ⟨h1, h2⟩ := hS
    specialize h2 (-B)
    simp at h2
    rw [neg_set_ge_bound] at hB
    simp [le_neg] at hB
    simp_all
    obtain ⟨x, this⟩ := this
    specialize hc x this
    specialize h1 (-x) (by simp [this])
    specialize hB (-x) (by simp [this])
    simp at hB h1
    sorry

lemma completeness_bounded_below (X : Set ℝ) [Nonempty X] : bound_below X → ∃ c, infimum X c := by
  intro h
  rename_i inst
  have hnempty : Nonempty (↑(-X)) := by
    obtain ⟨a, ha⟩ := inst
    use (-a)
    simp [ha]

  have hb := set_bound_above_neg_bound_below (-X)
  simp [h] at hb
  apply completeness_axiom_below X h

def func_bound_above (X : Set ℝ) (f : ℝ → ℝ) : Prop := (∃ (c : ℝ), ∀ x ∈ X, f x ≤ c)

def func_sup (X : Set ℝ) (f : ℝ → ℝ) (C : ℝ) : Prop := func_bound_above X f ∧ (∀ B, (∀ x ∈ X, f x ≤ B) → C ≤ B)
