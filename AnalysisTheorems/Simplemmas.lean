import Mathlib.Tactic

-- if ∀ ε > 0, a < b + ε then we can say that a ≤ b
lemma lt_add_imp_le (a b : ℝ) : (∀ ε > 0, a < b + ε) → a ≤ b := by
  intro h
  by_contra h1  -- assume a > b
  push_neg at h1
  rw [show b < a ↔ b - a < 0 by simp] at h1 -- show b - a < 0
  specialize h (a - b)  -- so use ε = a - b
  simp at h -- then this says b < a and a ≤ b which is clearly a contradiction
  linarith

-- if |a - b| < c then |a| ≤ |b| + c
lemma abs_sub_le_add (a b c : ℝ) : |a - b| < c → |a| ≤ |b| + c := by
  intro h
  have h1 := calc
      |a| = |a - b + b| := by simp
      _ ≤ |a - b| + |b| := by apply abs_add
  linarith

-- if |a| ≤ b then a ≤ b
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

-- if 0 < |a - b| then a ≠ b
lemma abs_nonneg_iff (a b : ℝ) : 0 < |a - b| ↔ a ≠ b := by
  rw [←sub_ne_zero, ←abs_ne_zero]
  norm_num
