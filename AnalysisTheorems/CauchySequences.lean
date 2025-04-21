import AnalysisTheorems.Subsequences

def seq_cauchy (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, ∀ m ≥ N, |x m - x n| < ε

theorem seq_cauchy_is_bounded (x : ℕ → ℝ) (hx : seq_cauchy x) : seq_bounded x := by
  specialize hx 1 (by norm_num)
  obtain ⟨N, hN⟩ := hx

  suffices (∀ n, |x n| ≤ M) by

theorem seq_conv_is_cauchy (x : ℕ → ℝ) (hx : ∃ l, seq_is_limit x l) : seq_cauchy x := by

  sorry

theorem seq_cauchy_is_conv (x : ℕ → ℝ) (hx : seq_cauchy x) : ∃ l, seq_is_limit x l := by
  sorry
