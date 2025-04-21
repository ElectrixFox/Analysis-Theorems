import AnalysisTheorems.Subsequences

def seq_cauchy (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, ∀ m ≥ N, |x m - x n| < ε

theorem seq_cauchy_is_bounded (x : ℕ → ℝ) (hx : seq_cauchy x) : seq_bounded x := by
  specialize hx 1 (by norm_num)
  obtain ⟨N, hN⟩ := hx

  have h1 : ∀ n ≥ N, |x n - x N| < 1 := by
    sorry

  have h2 : ∀ n ≥ N, |x n| ≤ |x n - x N| + |x N| ∧ |x n - x N| + |x N| < |x N| + 1 := by
    intro n hn
    specialize hN n hn
    sorry

  /-
  let C := |x| + 1
  let S : Finset ℝ := (Finset.range (N + 1)).image (fun n => |x n|)  -- getting the set x_1, ..., x_(N - 1)
  let P : ℝ := S.max' (by simp [S])
  let M := max P (|x N| + 1)

  suffices (∀ n, |x n| ≤ M) by
    constructor
    . -- M is the upper bound
      use M
      intro l hl
      simp at hl
      obtain ⟨n, hl⟩ := hl
      specialize this n
      simp_all
      apply abs_le_imp_le
      exact this
    . -- -M is the lower bound
      use -M
      intro l hl
      simp at hl
      obtain ⟨n, hl⟩ := hl
      specialize this n
      rw [←hl]
      rw [abs_le] at this
      apply this.left

  intro n
  dsimp [M]
  simp
  by_cases hN1 : n ≥ N
  . right
    calc
    |x n| = |x n - x N + x N| := by ring_nf
    _ ≤ |x n - x N| + |x N| := by apply abs_add
    _ ≤ |x N| + 1 := by
      rw [le_iff_lt_or_eq]
      left
      specialize h2 n hN1
      apply h2.right
  .
    simp at hN1
    sorry
  -/






theorem seq_conv_is_cauchy (x : ℕ → ℝ) (hx : ∃ l, seq_is_limit x l) : seq_cauchy x := by

  sorry

theorem seq_cauchy_is_conv (x : ℕ → ℝ) (hx : seq_cauchy x) : ∃ l, seq_is_limit x l := by
  sorry
