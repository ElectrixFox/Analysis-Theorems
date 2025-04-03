import AnalysisTheorems.Sequences

lemma e_def : (∃ l, seq_is_limit (fun (n : ℕ) => (1 + 1 / n) ^ n) l) := by sorry

noncomputable def exp : ℝ := e_def.choose -- gets the value of the limit

theorem seq_ex_def (x : ℕ) (hx : x > 0) : seq_is_limit (fun (n : ℕ) => (1 + x / n) ^ n) (exp ^ x) := by
  have hn (n : ℕ) (h1 : n > 0) : (1 + x / n) ^ n = (((n + x) / (n + x - 1)) : ℝ) ^ n * ((n + x - 1) / (n)) ^ n := by
    have hpos : ((n + x - 1) : ℝ) ≠ 0 := by admit

    calc
      ((1 + x / n) ^ n : ℝ) = ((n + x) / n) ^ n := by field_simp
      _ = (((n + x) / n) * ((n + x - 1) / (n + x - 1))) ^ n := by simp_all
      _ = (((n + x) / (n + x - 1) : ℝ) * ((n + x - 1) / n)) ^ n := by ring_nf
      _ = (((n + x) / (n + x - 1))) ^ n * ((n + x - 1) / (n)) ^ n := by field_simp
  conv =>
    lhs
    ext n

  sorry
