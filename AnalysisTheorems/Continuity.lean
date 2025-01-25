import Mathlib

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

example {a b : ℝ} (X : Set ℝ := generalInterval a b)(f : ℝ → ℝ) (c L : ℝ) : fun_point_limit X (fun x => 1 / x) 0 0 := by
  sorry

lemma lim_imp_left_right_lim {a b c L : ℝ} (hX : X = generalInterval a b) (f : ℝ → ℝ) :
  fun_point_limit X f c L →
  fun_left_limit₀ (generalInterval a c) f c L ∧
  fun_right_limit₀ (generalInterval c b) f c L := by
  sorry

example (f : ℝ → ℝ) (X : Set ℝ) (Y : open_interval 0 a): fun_limit_bound_below X f L → fun_right_limit Y f 0 := by
  intro h
  let x (t : ℝ) := 1 / t
  have : fun_right_limit Y x 0 := by
    intro ε hε
    use ε
    constructor
    simp
    linarith
    intro t h1 h2
    have : 0 < t := by
      obtain ⟨h1a, h2a⟩ := h1
      apply h1a     
    dsimp [x]
    simp
    field_simp
    simp [abs_of_pos, one_div_lt] at h2
    rw [abs_of_pos]
    rw [abs_of_pos] at h2
    calc
      1 / t ≤ t := by trivial
      _ < ε := by linarith
    rw [abs_of_pos]
    rw [one_div_lt]


    
  sorry

example (f : ℝ → ℝ) (hX : X = generalInterval (some a) (some b)): fun_limit_bound_below (generalInterval a none) f L → fun_right_limit₀ X f a 0 := by
  intro h
  let g : ℝ → ℝ := fun t => 1 / t
  have h1 : fun_point_limit X g a 0 := by
    sorry
  
  exact (lim_imp_left_right_lim hX f h1 0).2

  have : fun_right_limit₀ X (fun t => 1 / t) a 0 := by
    have h1 : fun_point_limit X (fun t => 1 / t) 0 0 := by
      sorry
    apply lim_imp_left_right_lim hX f h1 0
    intro ε hε
    use 1 / ε
    constructor
    simp
    linarith
    intro t h1 h2
    simp
    obtain ⟨ht1, ht2⟩ := h1
    simp at ht1 ht2
    clear ht2
    rw [abs_mid] at h2
    obtain ⟨hm1, hm2⟩ := h2
    rw [←one_div]
    rw [abs_div, abs_one, one_div_lt]


    have hc (a b : ℝ) (hb : 0 < b) (hab : b ≤ a) : |1 / a| < b → |a| > 1 / b := by
      intro h
      rw [gt_iff_lt, one_div_lt hb, ←abs_one, ←abs_div]
      apply h

      have :=
        calc
          0 < b := hb
          _ ≤ a := hab
      rw [abs_pos]
      linarith
    specialize hc t ε hε
    
    apply hc

    


    
  sorry
