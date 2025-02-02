import Mathlib

def lipschitz_cont (r : ℝ) (f : ℝ → ℝ) : Prop := ∃ M > 0, ∀ (x y : ℝ), r < x ∧ r < y → |f x - f y| ≤ M * |x - y|

def generalInterval [Preorder ℝ] (lower : Option ℝ) (upper : Option ℝ) : Set ℝ :=
  { x | (lower.map (fun a => a ≤ x)).getD True ∧ (upper.map (fun b => x ≤ b)).getD True }

def fun_point_limit (X : Set ℝ) (f : ℝ → ℝ) (c : ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X \ {c}, |x - c| < δ → |f x - L| < ε

def fun_right_limit (X : Set ℝ) (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x - a| < δ → |f x - L| < ε

def fun_left_limit (X : Set ℝ) (f : ℝ → ℝ) (b L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x - b| < δ → |f x - L| < ε

def open_interval (a b : ℝ) : Set ℝ := {x : ℝ | a < x ∧ b < x}

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

theorem intermediate_value_theorem (f : ℝ → ℝ) (hX : X = generalInterval (some a) (some b)) (ha : a < b) (hf : continuous_on f X) : (f b < f a ∧ d ∈ (generalInterval (f b) (f a))) ∨ (f a < f b ∧ d ∈ (generalInterval (f a) (f b))) → ∃ c ∈ X, f c = d := by
  sorry

theorem intermediate_value_theorem' (f : ℝ → ℝ) (hX : X = generalInterval (some a) (some b)) (ha : a < b) (hf : continuous_on f X) (hfb : f b < f a ∧ d ∈ (generalInterval (f b) (f a)) ∨ f a < f b ∧ d ∈ (generalInterval (f a) (f b))) : ∃ c ∈ X, f c = d := by
  sorry

theorem intermediate_value_theorem'' {a b : ℝ} {ha : a < b} (hX : X = {x | a ≤ x ∧ x ≤ b}) (f : ℝ → ℝ) (hf : continuous_on f {x | a ≤ x ∧ x ≤ b}) (hfb : f b < f a ∧ d ∈ {x | f b ≤ x ∧ x ≤ f a} ∨ f a < f b ∧ d ∈ {x | f a ≤ x ∧ x ≤ f b}) : ∃ c ∈ X, f c = d := by
  sorry

example : ∃ ξ ∈ {x | -1 ≤ x ∧ x ≤ 0}, (fun (x : ℝ) => 17 * x ^ 7 - 19 * x ^ 5 - 1) ξ = 0 := by
  let f x : ℝ := 17 * x ^ 7 - 19 * x ^ 5 - 1
  have hf : f = fun (x : ℝ) => 17 * x ^ 7 - 19 * x ^ 5 - 1 := by dsimp [f]
  rw [←hf]

  have hfcont : continuous_on f {x | -1 ≤ x ∧ x ≤ 0} := by sorry
    
  have hcond : (f 0 < f (-1) ∧ 0 ∈ (generalInterval (f 0) (f (-1)))) ∨ (f (-1) < f (0) ∧ 0 ∈ (generalInterval (f (-1)) (f (0)))) := by
    norm_num1
    dsimp [generalInterval]
    norm_num

  /-
  have def_intv : {(x : ℝ) | -1 ≤ x ∧ x ≤ 0} = generalInterval (-1 : ℝ) (0 : ℝ) := by dsimp [generalInterval]
  conv =>
    rw [def_intv]
  clear def_intv
  -/


  /-
  apply intermediate_value_theorem' f _ (by norm_num) hfcont hcond
  dsimp [generalInterval]
  -/
  /-
  apply intermediate_value_theorem' f ?_ _ hfcont hcond
  dsimp [generalInterval]
  simp
  -/
  apply intermediate_value_theorem'' _
  apply hfcont
  left
  norm_num
  norm_num
  rfl
  

example (hX : X = generalInterval (none) (none)): ∃ c, 1 < c ∧ c < 2 → (fun x => 2 * x ^ 3 - 3 * x ^ 2 + 7 * x - 9) c = 1 := by
  simp_all
  use 3 / 2
  intro h1 h2
  simp_all
