import Mathlib

def continuous (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

lemma abs_mid (a b c : ℝ) : |a - b| < c ↔ b - c < a ∧ a < b + c := by
  constructor <;> (rw [abs_lt]; intro h; (constructor <;> linarith))

lemma abs_mid_abs (a b c : ℝ) : |a - b| < c ↔ |b| - c < |a| ∧ |a| < |b| + c := by
  constructor
  .
    intro h
    constructor
    . 
      rw [abs_sub_comm] at h
      have :=
        calc
          |b| - |a| ≤ |a - b| := by rw [abs_sub_comm]; apply abs_sub_abs_le_abs_sub
          _ < c := by rw [abs_sub_comm]; apply h
      linarith
    . 
      have :=
        calc
          |a| - |b| ≤ |b - a| := by rw [abs_sub_comm]; apply abs_sub_abs_le_abs_sub
          _ < c := by rw [abs_sub_comm]; apply h
      linarith
  .
    intro h
    obtain ⟨h1, h2⟩ := h
    apply lt_add_of_sub_left_lt at h1
    rw [←neg_neg |a|, ←sub_eq_add_neg] at h1
    rw [lt_sub_iff_add_lt, ←sub_eq_add_neg] at h1
    rw [abs_sub_comm]
    apply lt_add_of_sub_left_lt at h1
    
        
    
    
    sorry

example (f : ℝ → ℝ) (c : ℝ) (a b : ℝ) (hc : a < c ∧ c < b) (hcn0 : f c ≠ 0) : continuous f c → ∃ δ > 0, ∀ x, (c - δ < x ∧ x < c + δ) → |f x| > |f c| / 2 := by
  intro hcont
  dsimp [continuous] at hcont
  obtain ⟨δ, hδ, hcon⟩ := hcont (|f c| / 2) (by positivity)
  clear hcont
  use δ
  constructor <;> try apply hδ
  intro x hx
  rw [gt_iff_lt]
  rw [←abs_mid] at hx
  specialize hcon x
  apply hcon at hx
  clear hcon
  have h2f : |f x| - |f c| < |f c| / 2 :=
      calc
        |f x| - |f c| ≤ |f x - f c| := by apply abs_sub_abs_le_abs_sub
        _ < |f c| / 2 := by linarith
  
  have h1 : 0 ≤ |f x - f c| ∧ |f x - f c| < |f c| / 2 := by
    constructor
    positivity
    linarith
  rw [abs_mid] at h1
  obtain ⟨ha1, ha2, ha3⟩ := h1
  by_cases hfc : (f c) < 0
  
  . 
    conv_lhs at ha2 =>
      rw [abs_of_neg hfc]
      ring_nf
    rw [abs_of_neg hfc]

    rw [←lt_add_neg_iff_lt]
    rw [←sub_eq_add_neg]
    rw [sub_neg_eq_add (|f x|) (f c / 2)]
    positivity

    calc
      f c / 2 < 0 := by
        cancel_denoms
        field_simp
      _ < |f x| := by positivity
    
    have : 0 < f x := by
      calc
        0 = -f c + f c := by sorry
        _ = f c - |f c| := by
          rw [abs_of_neg]
          simp
          
        _ < f x := by linarith
    ring_nf at ha3

  /-
  rw [sub_lt_iff_lt_add] at h2f
  ring_nf at h2f
  rw [abs_mid_abs] at hx
  linarith
  -/
