import AnalysisTheorems.Subsequences

lemma lt_add_imp_le (a b : ℝ) : (∀ ε > 0, a < b + ε) → a ≤ b := by
  intro h
  by_contra h1  -- assume a > b
  push_neg at h1
  rw [show b < a ↔ b - a < 0 by simp] at h1 -- show b - a < 0
  specialize h (a - b)  -- so use ε = a - b
  simp at h -- then this says b < a and a ≤ b which is clearly a contradiction
  linarith


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

theorem seq_COLT_scalarmult (x : ℕ → ℝ) (l : ℝ) (hx : seq_is_limit x l) (a : ℝ) : seq_is_limit (fun n => a * x n) (a * l) := by
  have := seq_COLT_linearity x (fun n => 0) l 0 hx (by simp_all [seq_is_limit]) a 0
  simp at this
  exact this

lemma conv_seq_bound_above_imp_lim_bound_above (x : ℕ → ℝ) (l : ℝ) (hx : seq_is_limit x l) (b : ℝ) : (∀ n, x n ≤ b) → l ≤ b := by
  intro h
  have h1 := seq_COLT_scalarmult x l hx (-1)
  simp at h1

  conv at h =>
    intro n
    rw [←neg_le_neg_iff]

  rw [←neg_le_neg_iff]
  apply conv_seq_bound_below_imp_lim_bound_below (fun n => -x n) _ (by simp_all)
  simp_all

lemma prop_1 (x : ℕ → ℝ) (hx : seq_bounded x) :
  ∃ c, minimum {l | ∃ (a : ℕ → ℕ), extraction a ∧ seq_is_limit (x ∘ a) l} c ∧
  ∃ C, maximum {l | ∃ (a : ℕ → ℕ), extraction a ∧ seq_is_limit (x ∘ a) l} C
  := by
  set L := {l | ∃ (a : ℕ → ℕ), extraction a ∧ seq_is_limit (x ∘ a) l}

  have Lnempty : Nonempty L := by
    by_contra h
    simp at h
    have h1 := subseq_BolzanoWeierstrass' x hx  -- get our converging subsequence
    obtain ⟨a, ha, l, hl⟩ := h1 -- getting the limit and the sequence
    simp [L] at h -- simplifying the set
    specialize h l a ha -- doing the needed specialisations
    exact h hl  -- showing exactly what is needed


  have Lbound : bounded L := by
    dsimp [seq_bounded] at hx
    obtain ⟨⟨c, hc⟩, ⟨C, hC⟩⟩ := hx
    dsimp [bounded]
    constructor
    .
      dsimp [L]
      use C
      intro xn hxn
      simp at hxn

    sorry
  sorry
