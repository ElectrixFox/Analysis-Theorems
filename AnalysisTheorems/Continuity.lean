import Sequences

/-
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

def seq_is_limit (x : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |x n - l| < ε

lemma conv_seq_bound_below_imp_lim_bound_below (x : ℕ → ℝ) (l : ℝ) (hx : seq_is_limit x l) (a : ℝ) : (∀ n, x n ≥ a) → l ≥ a := by
  dsimp [seq_is_limit] at hx
  intro h

  conv at hx =>
    intro ε hε  -- let ε > 0
    rhs
    ext N -- exists an N
    intro n hn  -- for any n ≥ N
    rw [abs_lt]
    rw [lt_sub_iff_add_lt, add_comm, ←sub_eq_add_neg]
    rhs
    rw [sub_eq_add_neg, ←lt_sub_iff_add_lt, sub_neg_eq_add, add_comm]
    -- l - ε < x n < l + ε

  have h1 : ∀ ε > 0, a < l + ε := by
    intro ε hε
    specialize hx ε hε  -- apply this to the limit definition
    obtain ⟨N, hN⟩ := hx  -- get our N
    specialize hN N -- use our N as the starting point
    simp at hN  -- get the inequality on its own
    specialize h N  -- now use x n ≥ a for all n
    linarith

  apply lt_add_imp_le
  exact h1

lemma conv_seq_bound_above_imp_lim_bound_above (x : ℕ → ℝ) (l : ℝ) (hx : seq_is_limit x l) (b : ℝ) : (∀ n, x n ≤ b) → l ≤ b := by
  dsimp [seq_is_limit] at hx
  intro h

  conv at hx =>
    intro ε hε  -- let ε > 0
    rhs
    ext N -- exists an N
    intro n hn  -- for any n ≥ N
    rw [abs_lt]
    rw [lt_sub_iff_add_lt, add_comm, ←sub_eq_add_neg] -- l - ε < x n < l + ε
  
  have h1 : ∀ ε > 0, l < b + ε := by
    intro ε hε
    specialize hx ε hε  -- apply this to the limit definition
    obtain ⟨N, hN⟩ := hx  -- get our N
    specialize hN N -- use our N as the starting point
    simp at hN  -- get the inequality on its own
    specialize h N  -- now use x n ≥ a for all n
    linarith

  apply lt_add_imp_le
  exact h1
-/

lemma seq_lim_in_closed_conv_closed {a b : ℝ} (hab : a < b) (x : ℕ → ℝ) (l : ℝ) (hxI : ∀ (n : ℕ), x n ∈ Set.Icc a b) (hx : seq_is_limit x l) : l ∈ Set.Icc a b := by
  by_contra h
  let ε := min (l - b) (a - l)
  have hε : ε > 0 := by -- since l ∉ [a, b] l < a or b < l as it has to be on one of the sides
    simp [ε]
    constructor
    . -- 0 < l - b
      simp at h
      apply h
      apply conv_seq_bound_below_imp_lim_bound_below x l hx a (by simp_all)
    . -- 0 < a - l
      contrapose h  -- easier to show contrapositive
      simp at *
      refine ⟨h, conv_seq_bound_above_imp_lim_bound_above x l hx b (by simp_all)⟩

  specialize hx ε hε
  obtain ⟨N, hN⟩ := hx
  have hε1 : 0 < l - b := by simp_all [ε]
  have hε2 : 0 < a - l := by simp_all [ε]
  suffices (∀ n, x n ∉ Set.Icc a b) by simp_all -- suffices to show that x n ∉ [a, b] for all n ≥ N since ε > 0 then b < l and l < a
  linarith  -- linearity
