import AnalysisTheorems.Sequences

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

def seq_dec (x : ℕ → ℝ) : Prop := ∀ n, x (n + 1) ≤ x n

lemma seq_bound_imp_subseq_bound (x : ℕ → ℝ) (a : ℕ → ℕ) (ha : extraction a) : seq_bounded x → seq_bounded (x ∘ a) := by
  intro h
  dsimp [seq_bounded, bound_above] at * -- simplify the definitions
  simp_all  -- simplify further
  obtain ⟨c, h⟩ := h  -- get our upper bound from the hypothesis
  use c -- use this upper bound
  intro j -- get the new variable
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

lemma abs_le_imp_le (a b : ℝ) : |a| ≤ b → a ≤ b := by
  intro h
  by_cases h1 : a ≤ 0
  .
    rw [abs_of_nonpos h1] at h
    linarith
  .
    push_neg at h1
    rw [abs_of_pos h1] at h
    exact h

lemma set_bound_above_neg_bound_below (X : Set ℝ) : bound_above X ↔ bound_below (-X) := by
  constructor
  repeat' -- repeat this as the following works in both ways
  . intro h
    obtain ⟨c, hc⟩ := h -- get the upper (lower) bound
    use (-c)  -- the lower (upper) bound is -c since c is positive
    intro x
    specialize hc (-x)  -- the x in X will be -x since x is -ve
    simp_all [neg_le, le_neg] -- cleaning up the inequalities


/-- Given a bounded sequence `x : ℕ → ℝ`, define `seq_sup` as the sequence of supremums of the tail sets. -/
noncomputable
def seq_sup (x : ℕ → ℝ) (hx : seq_bounded x) : ℕ → ℝ := fun n =>
  let S := {xm | ∃ m : ℕ, m ≥ n ∧ xm = |x m|}
  have hS1 : bound_above S := by
    obtain ⟨c, hc⟩ := hx
    use c
    intro y hy
    obtain ⟨m, hm, hy_eq⟩ := hy
    simp_all
  have hS2 : Nonempty S := by simp [Set.Nonempty.of_subtype, S]; tauto
  (completeness_axiom S hS1).choose

/-- Given a bounded sequence `x : ℕ → ℝ`, define `seq_inf` as the sequence of infimums of the tail sets. -/
noncomputable
def seq_inf (x : ℕ → ℝ) (hx : seq_bounded x) : ℕ → ℝ := fun n =>
  let S := {xm | ∃ m : ℕ, m ≥ n ∧ xm = |x m|}
  have hS1 : bound_below S := by
    obtain ⟨c, hc⟩ := hx
    use 0
    intro y hy
    obtain ⟨m, hm, hy_eq⟩ := hy
    simp_all
  have : (-S) = { -xm | xm ∈ S } := by
    ext a
    constructor
    . intro h
      use (-a)
      simp
      tauto
    . intro h
      simp at h
      obtain ⟨b, h⟩ := h
      simp [←h.right, h.left]
  have hS3 : bound_above { -xm | xm ∈ S } := by rw [←this, set_bound_above_neg_bound_below (-S)]; simp [hS1]
  have hS2 : Nonempty { -xm | xm ∈ S } := by simp [Set.Nonempty.of_subtype]; tauto
  let neg_inf := (completeness_axiom { -xm | xm ∈ S } hS3).choose;
  -neg_inf

/-
noncomputable
def seq_sup (x : ℕ → ℝ) (hx : seq_bound_above x) : ℕ → ℝ := fun n =>
  let S := {xm | ∃ m : ℕ, m ≥ n ∧ xm = x m}

  have hS1 : bound_above S := by
    obtain ⟨c, hc⟩ := hx
    use c
    intro y hy
    obtain ⟨m, hm, hy_eq⟩ := hy
    simp_all
  have hS2 : Nonempty S := by simp [Set.Nonempty.of_subtype, S]; tauto  -- obviously if is bounded above then it will be nonempty

  (completeness_axiom S hS1).choose

noncomputable
def seq_inf (x : ℕ → ℝ) (hx : seq_bound_below x) : ℕ → ℝ := fun n =>
  let S := {xm | ∃ m : ℕ, m ≥ n ∧ xm = x m}

  have hS1 : bound_below S := by
    obtain ⟨c, hc⟩ := hx
    use c
    intro y hy
    obtain ⟨m, hm, hy_eq⟩ := hy
    simp_all

  have : (-S) = { -xm | xm ∈ S } := by
    ext a
    constructor
    . intro h
      use (-a)
      simp
      tauto
    . intro h
      simp at h
      obtain ⟨b, h⟩ := h
      simp [←h.right, h.left]

  have hS3 : bound_above { -xm | xm ∈ S } := by rw [←this, set_bound_above_neg_bound_below (-S)]; simp [hS1]
  have hS2 : Nonempty { -xm | xm ∈ S } := by simp [Set.Nonempty.of_subtype]; tauto  -- obviously if is bounded above then it will be nonempty
  let neg_inf := (completeness_axiom { -xm | xm ∈ S } hS3).choose;
  -neg_inf
-/

lemma seq_infseq_le_supseq (x : ℕ → ℝ) (hx : seq_bounded x) :
  (seq_mono_dec (seq_sup x hx) ∧ seq_bounded (seq_sup x hx)) ∧
  (seq_mono_inc (seq_inf x hx) ∧ seq_bounded (seq_inf x hx)) := by
  constructor
  .
    constructor
    .
      -- Prove that seq_sup is monotonically decreasing
      dsimp [seq_sup]
      intro n m hnm
      let Sn := {xm | ∃ k : ℕ, k ≥ n ∧ xm = |x k|}
      let Sm := {xm | ∃ k : ℕ, k ≥ m ∧ xm = |x k|}
      have hsub : Sm ⊆ Sn := by
        intro y hy
        obtain ⟨k, hk1, hk2⟩ := hy
        use k
        constructor
        .
          rw [ge_iff_le] at *
          subst hk2
          rw [le_iff_lt_or_eq] at hnm
          obtain h1 | h2 := hnm
          . sorry
          . simp_all only [h2]

          sorry
        . exact hk2
      have hSn : bound_above Sn := by
        obtain ⟨c, hc⟩ := hx
        use c
        intro y hy
        obtain ⟨k, hk1, hk2⟩ := hy
        simp_all
      have hSm : bound_above Sm := by
        obtain ⟨c, hc⟩ := hx
        use c
        intro y hy
        obtain ⟨k, hk1, hk2⟩ := hy
        simp_all
      sorry
      -- have hle := completeness_axiom_subset Sm Sn hSm hSn hsub
      -- exact hle
    .
      -- Prove that seq_sup is bounded
      dsimp [seq_sup, seq_bounded]
      obtain ⟨c, hc⟩ := hx
      use c
      intro n
      let Sn := {xm | ∃ k : ℕ, k ≥ n ∧ xm = |x k|}
      have hSn : bound_above Sn := by
        use c
        intro y hy
        obtain ⟨k, hk1, hk2⟩ := hy
        simp_all
      sorry
      -- exact (completeness_axiom Sn hSn).choose_spec.left
  .
    constructor
    .
      -- Prove that seq_inf is monotonically increasing
      dsimp [seq_inf]
      intro n m hnm
      let Sn := {xm | ∃ k : ℕ, k ≥ n ∧ xm = |x k|}
      let Sm := {xm | ∃ k : ℕ, k ≥ m ∧ xm = |x k|}
      have hsub : Sn ⊆ Sm := by
        intro y hy
        obtain ⟨k, hk1, hk2⟩ := hy
        use k
        constructor
        . sorry -- linarith
        . exact hk2
      have hSn : bound_below Sn := by
        use 0
        intro y hy
        obtain ⟨k, hk1, hk2⟩ := hy
        simp_all
      have hSm : bound_below Sm := by
        use 0
        intro y hy
        obtain ⟨k, hk1, hk2⟩ := hy
        simp_all
      sorry
      -- have hle := completeness_axiom_subset (-Sn) (-Sm) (set_bound_above_neg_bound_below Sn hSn) (set_bound_above_neg_bound_below Sm hSm) (fun x hx => hsub (-x) hx)
      -- simp at hle
      -- exact hle
    .
      -- Prove that seq_inf is bounded
      dsimp [seq_inf, seq_bounded]
      obtain ⟨c, hc⟩ := hx
      use c
      intro n
      let Sn := {xm | ∃ k : ℕ, k ≥ n ∧ xm = |x k|}
      have hSn : bound_below Sn := by
        use 0
        intro y hy
        obtain ⟨k, hk1, hk2⟩ := hy
        simp_all
      sorry
      -- exact (completeness_axiom (-Sn) (set_bound_above_neg_bound_below Sn hSn)).choose_spec.left.neg


lemma seq_infseq_le_supseq' (x : ℕ → ℝ) (hx : seq_bounded x) :
  (seq_mono_dec (seq_sup x hx) ∧ seq_bounded (seq_sup x hx)) ∧
  (seq_mono_inc (seq_inf x hx) ∧ seq_bounded (seq_inf x hx)) ∧
  (∃ ls, seq_is_limit (seq_sup x hx) ls ∧
  ∃ li, seq_is_limit (seq_inf x hx) li → li ≤ ls) := by
  let xSup := seq_sup x hx
  let xInf := seq_inf x hx
  have hSup : xSup = seq_sup x hx := rfl
  have hInf : xInf = seq_inf x hx := rfl
  rw [←hSup, ←hInf]

  obtain ⟨C, hC⟩ := hx
  have h1 : ∃ c < C, ∀ (n : ℕ), x n ∈ {x : ℝ | c < x ∧ x < C}
  let Xn := {xm : ℝ | ∃ (n : ℕ), ∃ (m : ℕ), m ≥ n ∧ xm = x m}
  have hXb : bounded Xn := by
    suffices h : seq_bounded x from by
      -- there exists an x ∈ xₙ such that for all x ∈ Xn, x ≤ x₀
      have h1 : ∀ xn ∈ Xn, ∃ (n : ℕ), xn ≤ x n := by
        intro xn hxn
        dsimp [Xn] at hxn
        obtain ⟨n, m, hnm1, hnm2⟩ := hxn
        subst hnm2
        simp_all
        apply Exists.intro
        rfl

      clear h1
      -- there exists an x ∈ xₙ such that for all x ∈ Xn, x ≤ x₀
      have h2 : ∃ (n : ℕ), ∀ xn ∈ Xn, |xn| ≤ x n := by

        use 2
        intro xn hxn
        dsimp [Xn] at hxn
        obtain ⟨n, m, hnm1, hnm2⟩ := hxn
        subst hnm2
        simp_all
        sorry
      dsimp [bounded]
      obtain ⟨n, hn⟩ := h2
      use (x n)
    tauto
  constructor
  .
    constructor
    .
      sorry

    .
      sorry
  constructor
  .
    sorry

  sorry
