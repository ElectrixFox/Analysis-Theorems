import AnalysisTheorems.Sequences

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

def seq_dec (x : ℕ → ℝ) : Prop := ∀ n, x (n + 1) ≤ x n

lemma seq_bound_imp_subseq_bound (x : ℕ → ℝ) (a : ℕ → ℕ) (ha : extraction a) : seq_bounded x → seq_bounded (x ∘ a) := by
  intro h
  constructor
  .
    dsimp [seq_bounded, bound_above] at * -- simplify the definitions
    simp_all  -- simplify further
    obtain ⟨c, h⟩ := h.left  -- get our upper bound from the hypothesis
    use c -- use this upper bound
    intro j -- get the new variable
    specialize h (x (a j))  -- specialise the element in the sequence to being any subsequence element
    simp at h -- simplify some stuff
    apply h -- apply the hypothesis
  .
    dsimp [seq_bounded, bound_below] at * -- simplify the definitions
    simp_all  -- simplify further
    obtain ⟨c, h⟩ := h.right  -- get our lower bound from the hypothesis
    use c -- use this lower bound
    intro j -- get the new variable
    specialize h (x (a j))  -- specialise the element in the sequence to being any subsequence element
    simp at h -- simplify some stuff
    apply h -- apply the hypothesis

lemma subseq_ge_index (a : ℕ → ℕ) (ha : extraction a) : ∀ j, a j ≥ j := by
  intro j
  induction' j with k hk
  . norm_num
  .
    rw [ge_iff_le] at *
    calc
      k + 1 = k + 1 := rfl
      _ ≤ a k + 1 := by
        linear_combination hk -- this closes it in one since it shows how this is just a combination of hk
      _ ≤ a (k + 1) := by --  tauto also closes this goal in one step
        dsimp [extraction] at ha
        specialize ha k (k + 1) -- specializing the extraction to k and k + 1
        simp at ha  -- showing it says a k < a (k + 1)
        linarith  -- linearity does the rest

lemma subseq_conv_to_seq_limit (x : ℕ → ℝ) (a : ℕ → ℕ) (l : ℝ) (hx : seq_is_limit x l) (ha : extraction a) : seq_is_limit (x ∘ a) l := by
  intro ε hε
  rcases hx ε hε with ⟨N, hN⟩ -- gets all the stuff we need
  use N -- use the N from the main sequence
  intro n hn

  have h1 : a n ≥ N := by linarith [subseq_ge_index a ha n]  -- a n ≥ N then linearity of N ≥ n

  specialize hN (a n) h1  -- use the specialisation
  simp [hN] -- complete the goal

lemma seq_contsub_inc_or_dec (x : ℕ → ℝ) : ∃ a : ℕ → ℕ, extraction a ∧ (seq_mono_inc (x ∘ a) ∨ seq_mono_dec (x ∘ a)) := by
  let P := {n0 : ℕ | ∀ n > n0, x n0 ≥ x n}  -- the set of "peak" indices

  by_cases h : P.Infinite -- there can either be an infinite or finite number of peak indices
  . -- infinitely many peak indices
    sorry
  . -- finitely many peak indices
    sorry


theorem subseq_BolzanoWeierstrass (x : ℕ → ℝ) (hx : seq_bounded x) : ∃ a, extraction a → ∃ l, seq_is_limit (x ∘ a) l := by
  have := seq_contsub_inc_or_dec x
  obtain ⟨a, ha⟩ := this
  use a
  intro h1
  simp [h1] at ha
  obtain ha1 | ha2 := ha
  repeat' -- repeatedly apply the following logic
  . apply seq_mono_bound_conv (x ∘ a) -- if the sequence is monotone and bounded then it converges
    apply seq_bound_imp_subseq_bound x a h1 hx -- the sequence is bounded so the subsequence is bounded
    tauto -- show that it is true by True ∨ something is always true

theorem subseq_BolzanoWeierstrass' (x : ℕ → ℝ) (hx : seq_bounded x) : ∃ a, extraction a ∧ ∃ l, seq_is_limit (x ∘ a) l := by
  have := seq_contsub_inc_or_dec x
  obtain ⟨a, ha⟩ := this
  use a -- use our newly found extraction
  simp [ha.left]  -- as we know it is an extraction we can get rid of that
  obtain ⟨ha, ha1 | ha2⟩ := ha
  repeat' -- repeatedly apply the following logic
  . apply seq_mono_bound_conv (x ∘ a) -- if the sequence is monotone and bounded then it converges
    apply seq_bound_imp_subseq_bound x a ha hx -- the sequence is bounded so the subsequence is bounded
    tauto -- show that it is true by True ∨ something is always true

lemma set_bound_above_neg_bound_below (X : Set ℝ) : bound_above X ↔ bound_below (-X) := by
  constructor
  repeat' -- repeat this as the following works in both ways
  . intro h
    obtain ⟨c, hc⟩ := h -- get the upper (lower) bound
    use (-c)  -- the lower (upper) bound is -c since c is positive
    intro x
    specialize hc (-x)  -- the x in X will be -x since x is -ve
    simp_all [neg_le, le_neg] -- cleaning up the inequalities
