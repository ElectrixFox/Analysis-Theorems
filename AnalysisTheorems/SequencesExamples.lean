import AnalysisTheorems.Sequences

example : seq_is_limit (fun n => 6) 6 := by
  intro ε hε
  use 6
  simp [hε]

example (a : ℕ → ℝ) (ha : a = ((fun n => 1 / n) : ℕ → ℝ)) : seq_is_limit a 0 := by
  intro ε hε
  have h1 : ∃ (N : ℕ), N * ε > 1 := by exact archimedes _ _ hε  -- use archimedes to show there is a natural

  have h2 : ∃ (N : ℕ), N > 1 / ε := by  -- show that this natural is manipulable
    conv_rhs at h1 => ext N; rw [gt_iff_lt, ←div_lt_iff₀ hε, ←gt_iff_lt]
    exact h1

  obtain ⟨N, hN⟩ := h2
  use N
  intro n hn
  subst a

  simp [←one_div]
  have : 0 < n := by
    have h0 : (0 : ℝ) < N := by
      calc
        0 < 1 / ε := by positivity
        _ < N := by linarith
    suffices h : (0 < N) from by linarith
    field_simp at h0
    linarith

  rw [abs_of_nonneg (by simp)]
  rw [one_div_lt (by positivity) (by positivity)]
  calc
    1 / ε < N := hN
    _ ≤ n := by simp_all

example : seq_is_limit (fun (n : ℕ) => (-1) ^ n / (√(n ^ 2 + n))) 0 := by
  have h : ∀ (n : ℕ), |(fun (n : ℕ) => (-1) ^ n / (√(n ^ 2 + n))) n| ≤ (fun (n : ℕ) => 1 / √(n)) n := by
    admit
    /-
    intro n
    simp [←one_div]
    calc
      |(-1) ^ n / (√(n ^ 2 + n))| = 1 / (√(n ^ 2 + n)) := by admit
      _ ≤ 1 / √(n + n) := by admit
      _ ≤ 1 / √(n) := by admit
    -/
  have h1 : seq_is_limit (fun (n : ℕ) => 1 / √(n)) 0 := by sorry
  exact seq_squeeze_zero (fun (n : ℕ) => (-1) ^ n / (√(n ^ 2 + n))) (fun (n : ℕ) => 1 / √(n)) h1 h


example : even_subs' (fun n ↦ (-1) ^ n * (1 - 1 / n)) = fun (n : ℕ) ↦ (1 - 1 / (2 * n) : ℝ) := by
  ext x
  dsimp [even_subs', even_subs'.eseq]
  norm_num

example (x : ℕ → ℝ) (a : ℕ → ℕ)
  (ha : a = fun n ↦ 2 * n)
  (hx : x = fun (n : ℕ) ↦ ((-1) ^ n * (1 - 1 / n) : ℝ))
  (has : subseq a)
  : subseq_bijection x a has = fun (n : ℕ) ↦ (1 - 1 / (2 * n) : ℝ) := by
  ext y
  dsimp [subseq_bijection]
  rw [hx, ha]
  norm_num
