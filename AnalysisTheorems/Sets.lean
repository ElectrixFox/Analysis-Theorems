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

def infimum (X : Set ℝ) (c : ℝ) := (∀ x ∈ X, c ≤ x) ∧ (∀ b, (∀ x ∈ X, b ≤ x) → b ≤ c)


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

theorem bernoulli_inequality (x : ℝ) (n : ℕ) (hn₀ : n ≥ 1) (hx : x ≥ -1) : (1 + x) ^ n ≥ 1 + n * x := by
  by_cases h : x = -1
  .
    rw [h]
    norm_num
    rw [zero_pow (by linarith), zero_add]
    norm_cast
  .
    push_neg at h
    rw [ge_iff_le, le_iff_lt_or_eq] at hx
    obtain hx | hx := hx
    .
      induction' n, hn₀ using Nat.le_induction with k hn hk
      . simp
      . rw [pow_add]
        rw [ge_iff_le] at *
        have h1 := calc
          (1 + x) * (1 + k * x) ≤ (1 + x) * (1 + x) ^ k := by
            gcongr (1 + x) * ?_
            linarith
          _= (1 + x) ^ (k + 1) := by ring_nf
        nth_rw 1 [mul_add] at h1
        rw [pow_add] at h1
        conv_lhs at h1 => ring_nf
        rw [←mul_comm]
        have h2 : 1 + x * ↑(k + 1) ≤ 1 + x + x * k + x ^ 2 * k := by
            rify
            rw [mul_add, mul_one, add_comm (x * k), ←add_assoc]
            simp
            positivity
        exact le_trans h2 h1
    . tauto


axiom completeness_axiom (X : Set ℝ) [Nonempty X] : bound_above X → ∃ C, supremum X C

lemma pow_lt_pow_iff (a b : ℝ) (p : ℕ) (hp : p ≥ 1) (hab : a ≥ 0 ∧ b ≥ 0) : a < b ↔ a ^ p < b ^ p := by
  constructor
  pick_goal 2
  contrapose
  push_neg
  all_goals
  .
    intro h
    gcongr
    linarith

theorem exists_pth_root (p a : ℕ) (hp : p ≥ 1) (ha : a ≥ 0) : ∃! x ≥ 0, x ^ p = a := by
  by_cases h : a = 0
  .
    refine ⟨0, ?_⟩
    constructor
    simp only [ge_iff_le, le_refl, true_and, h]

    rw [zero_pow (by linarith)]
    simp
    intro y h0
    rw [h] at h0
    rw [pow_eq_zero_iff (by linarith)] at h0
    exact h0
  .
    push_neg at h
    conv at ha =>
      rw [ge_iff_le, le_iff_eq_or_lt]
      simp [h.symm]
    clear h
    have pow_ineq (x y : ℝ) : 0 < x ∧ x < y → x ^ p < y ^ p := by
      intro h
      obtain ⟨hx, hy⟩ := h
      rw [pow_lt_pow_iff_left₀] <;> linarith

    set A := {x : ℝ | x ^ p < a}
    have (x : ℝ) (hx : x ∈ A) := calc
      x ^ p < a := hx
      _ < 1 + p * a := by
        rw [add_comm]
        apply lt_add_of_tsub_lt_left
        nth_rw 1 [mul_comm, ←mul_one a]
        push_cast
        rw [←mul_sub_left_distrib]
        rw [←lt_add_neg_iff_lt]
        rw [←mul_neg_one]
        rw [show (0 < 1 + a * (1 - p) * (-1 : ℝ) ↔ 0 < 1 + a * (p - 1)) by sorry]
        positivity
      _ ≤ (1 + a) ^ p := by
        apply bernoulli_inequality <;> linarith

    conv at this =>
      intro x hx
      rw [←pow_lt_pow_iff x (1 + ↑a) p hp]
    

lemma set_bound_above_neg_bound_below (X : Set ℝ) : bound_above X ↔ bound_below (-X) := by
  constructor
  repeat' -- repeat this as the following works in both ways
  . intro h
    obtain ⟨c, hc⟩ := h -- get the upper (lower) bound
    use (-c)  -- the lower (upper) bound is -c since c is positive
    intro x
    specialize hc (-x)  -- the x in X will be -x since x is -ve
    simp_all [neg_le, le_neg] -- cleaning up the inequalities


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

theorem completeness_axiom_below (X : Set ℝ) [Nonempty X] : bound_below X → ∃ c, infimum X c := by
  intro h
  have h1 : bound_below X ↔ bound_above (-X) := by
    have := set_bound_above_neg_bound_below (-X)
    simp at this
    exact this.symm

  set S := -X
  have : Nonempty S := by
    simp [S]
    rename_i i
    obtain ⟨x, hx⟩ := i
    use (-x)
    simp [hx]
  rw [h1] at h
  have h0 := inf_of_neg_eq_neg_sup S h
  have := completeness_axiom S h
  obtain ⟨C, hC⟩ := this
  specialize h0 (-C)
  simp [hC] at h0
  use -C
  simp [S] at h0
  exact h0

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
