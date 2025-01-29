import Mathlib

def lipschitz_cont (r : ℝ) (f : ℝ → ℝ) : Prop := ∃ M > 0, ∀ (x y : ℝ), r < x ∧ r < y → |f x - f y| ≤ M * |x - y|

lemma abs_nonneg_iff (a b : ℝ) (hab : 0 < a ∧ 0 < b) : 0 < |a - b| ↔ a ≠ b := by
  constructor
  . contrapose
    simp
    intro h
    linarith
  . contrapose
    intro h
    simp
    simp at h
    linarith
    
  
example : ∀ (r : ℝ), r > 0 → lipschitz_cont r (fun x => 1 / x) := by
  intro r hr
  use (1 / |r|)
  constructor
  . positivity
  intro x y hxy
  obtain ⟨hx, hy⟩ := hxy
  simp [←one_div]
  
  by_cases hxy : x = y
  simp [hxy]
  push_neg at hxy

  have hin : 1 / |x * y| ≤ 1 / |r| := by
    rw [one_div_le]
    simp
    rw [le_mul]
  calc
    |1 / x - 1 / y| = |(y - x) / (x * y)| := by
      rw [sub_div]
      rw [div_mul_cancel_left₀, ←one_div]
      rw [div_mul_cancel_right₀, ←one_div]
      linarith
      linarith
    _ = |y - x| / |x * y| := by rw [abs_div]
    _ = |x - y| / |x * y| := by rw [abs_sub_comm]
    _ ≤ |x - y| / |r| := by
      rw [←one_div_mul_eq_div, mul_comm]
      rw [←one_div_mul_eq_div |r|, mul_comm (1 / |r|)]
      rw [mul_le_mul_left]
      apply hin
      rw [abs_nonneg_iff]
      apply hxy
      constructor <;> linarith
    
  
