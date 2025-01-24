import Mathlib

def continuous (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

def continuous_on (f : ℝ → ℝ) (X : Set ℝ) : Prop :=
  ∀ x, x ∈ X → continuous f x

lemma abs_mid (a b c : ℝ) : |a - b| < c ↔ b - c < a ∧ a < b + c := by
  constructor <;> (rw [abs_lt]; intro h; (constructor <;> linarith))

lemma abs_neg_lt (a b : ℝ) (ha : b < 0) : a < b → |b| < |a| := by
  intro h
  have : a < 0 := by linarith
  repeat rw [abs_of_neg]
  simp [h]
  repeat linarith

example (f : ℝ → ℝ) (c : ℝ) (hcn0 : f c ≠ 0) : continuous f c → ∃ δ > 0, ∀ x, (c - δ < x ∧ x < c + δ) → |f x| > |f c| / 2 := by
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
  rw [abs_mid] at hx
  obtain ⟨h1, h2⟩ := hx
  by_cases hfcp : f c ≥ 0
  . 
    rw [abs_of_nonneg hfcp] at h1
    ring_nf at h1
    field_simp at h1
    have h1p : 0 ≤ f x := by linarith
    repeat rw [abs_of_nonneg]
    apply h1
    repeat linarith
  . 
    simp at hfcp
    rw [abs_of_neg hfcp] at h2
    ring_nf at h2
    field_simp at h2
    apply abs_neg_lt at h2 <;> try linarith
    rw [abs_div] at h2
    simp at h2
    apply h2

example (f : ℝ → ℝ) (c : ℝ) (hcn0 : f c ≠ 0) {a b : ℝ} (hc : c ∈ {x : ℝ | a < x ∧ x < b}) : continuous_on f ({x : ℝ | a < x ∧ x < b}) → ∃ δ > 0, ∀ x, (c - δ < x ∧ x < c + δ) → |f x| > |f c| / 2 := by
  intro hcont
  dsimp [continuous_on] at hcont
  specialize hcont c
  simp at hcont
  obtain ⟨h1, h2⟩ := hc
  simp [h1, h2] at hcont
  clear h1 h2
  
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
  rw [abs_mid] at hx
  obtain ⟨h1, h2⟩ := hx
  by_cases hfcp : f c ≥ 0
  . 
    rw [abs_of_nonneg hfcp] at h1
    ring_nf at h1
    field_simp at h1
    have h1p : 0 ≤ f x := by linarith
    repeat rw [abs_of_nonneg]
    apply h1
    repeat linarith
  . 
    simp at hfcp
    rw [abs_of_neg hfcp] at h2
    ring_nf at h2
    field_simp at h2
    apply abs_neg_lt at h2 <;> try linarith
    rw [abs_div] at h2
    simp at h2
    apply h2
