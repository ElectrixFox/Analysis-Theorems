import Mathlib

def lipschitz_cont (r : ℝ) (f : ℝ → ℝ) : Prop := ∃ M > 0, ∀ (x y : ℝ), r < x ∧ r < y → |f x - f y| ≤ M * |x - y|

def generalInterval [Preorder ℝ] (lower : Option ℝ) (upper : Option ℝ) : Set ℝ :=
  { x | (lower.map (fun a => a ≤ x)).getD True ∧ (upper.map (fun b => x ≤ b)).getD True }

def fun_point_limit (X : Set ℝ) (f : ℝ → ℝ) (c : ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X \ {c}, |x - c| < δ → |f x - L| < ε

def fun_right_limit₀ (X : Set ℝ) (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x - a| < δ → |f x - L| < ε

def fun_left_limit₀ (X : Set ℝ) (f : ℝ → ℝ) (b L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x - b| < δ → |f x - L| < ε

def open_interval (a b : ℝ) : Set ℝ := {x : ℝ | a < x ∧ b < x}

def fun_right_limit (X : open_interval a b) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ (open_interval a b), |x - a| < δ → |f x - L| < ε

def fun_left_limit (X : open_interval a b) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ (open_interval a b), |x - b| < δ → |f x - L| < ε

def fun_limit_bound_below (X : Set ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ K > 0, ∀ x ∈ X, x ≥ K → |f x - L| < ε

def fun_limit_bound_above (X : Set ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ K > 0, ∀ x ∈ X, x ≤ K → |f x - L| < ε

def continuous (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

def continuous_on (f : ℝ → ℝ) (X : Set ℝ) : Prop :=
  ∀ x, x ∈ X → continuous f x

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
  use (1 / |r ^ 2|)
  constructor
  . positivity
  intro x y hxy
  obtain ⟨hx, hy⟩ := hxy
  simp [←one_div]
  
  by_cases hxy : x = y
  simp [hxy]
  push_neg at hxy

  have h1 : 0 < x := by linarith
  have h2 : 0 < y := by linarith
  have h3 : 0 < x * y := by positivity

  have hin : 1 / |x * y| ≤ 1 / r ^ 2 := by
    rw [one_div_le]
    simp

    rw [abs_of_pos] <;> try linarith
    
    . 
      rw [pow_two]
      rel [hx, hy]
    . apply abs_pos_of_pos
      simp_all
    . simp_all
    
  rw [one_div_mul_eq_div]
  calc
    |1 / x - 1 / y| = |(y - x) / (x * y)| := by
      rw [sub_div]
      rw [div_mul_cancel_left₀, ←one_div]
      rw [div_mul_cancel_right₀, ←one_div]
      linarith
      linarith
    _ = |y - x| / |x * y| := by rw [abs_div]
    _ = |x - y| / |x * y| := by rw [abs_sub_comm]
    _ ≤ |x - y| / r ^ 2 := by
      rw [←one_div_mul_eq_div, mul_comm]
      rw [←one_div_mul_eq_div (r ^ 2), mul_comm (1 / r ^ 2)]
      rw [mul_le_mul_left]
      apply hin
      rw [abs_nonneg_iff]
      apply hxy
      constructor <;> linarith
  

theorem intermediate_value_theorem (hX : X = generalInterval (some a) (some b)) (ha : a < b) (f : ℝ → ℝ) (hf : continuous_on f X) : (f b < f a ∧ d ∈ (generalInterval (f b) (f a))) ∨ (f a < f b ∧ d ∈ (generalInterval (f a) (f b))) → ∃ c ∈ X, f c = d := by
  sorry

example (hX : X = generalInterval (none) (none)): ∃ c, 1 < c ∧ c < 2 → (fun x => 2 * x ^ 3 - 3 * x ^ 2 + 7 * x - 9) c = 1 := by
  simp_all
  use 3 / 2
  intro h1 h2
  simp_all
