import AnalysisTheorems.Subsequences

lemma lem_1 (a b : ℝ) : (∀ ε > 0, a < b + ε) → a ≤ b := by
  intro h
  by_contra h1  -- assume a > b
  push_neg at h1
  rw [show b < a ↔ b - a < 0 by simp] at h1 -- show b - a < 0
  specialize h (a - b)  -- so use ε = a - b
  simp at h -- then this says b < a and a ≤ b which is clearly a contradiction
  linarith


lemma thm_1 (x : ℕ → ℝ) (l : ℝ) (hx : seq_is_limit x l) (a : ℝ) : ∀ n, x n ≥ a → l ≥ a := by
  dsimp [seq_is_limit] at hx
  intro n hn

  conv at hx =>
    intro ε hε
    rhs
    ext N
    intro n hn
    rw [abs_lt]
    rw [lt_sub_iff_add_lt, add_comm, ←sub_eq_add_neg]
    rhs
    rw [sub_eq_add_neg, ←lt_sub_iff_add_lt, sub_neg_eq_add, add_comm]

  have h1 (a b : ℝ) : ∀ ε > 0, a < b + ε → a ≤ b := by
    intro ε hε
    by_contra h
    simp at h
    aesop
    rw [lt_add_of_le_of_pos]
    aesop?
    rw [le_iff_lt_or_eq]
    apply le_add_of_le_left
    obtain ⟨ε, hε, h1, h2⟩ := h

    by_contra h
    simp at h


  rw [ge_iff_le]
  calc
    a ≤ x n := by exact hn
    _ ≤ l := by
      conv at hx =>
        intro ε hε
        rhs
        ext N
        intro n hn
        right





lemma prop_1 (x : ℕ → ℝ) (hx : seq_bounded x)
  (L : Set ℝ := {l | ∃ (a : ℕ → ℕ), extraction a ∧ seq_is_limit (x ∘ a) l}) :
  ∃ c, minimum L c ∧ ∃ C, maximum L C
  := by
  have Lbound : bounded L := by
    sorry
  sorry

/-
lemma seq_bound_min_max_limit (x : ℕ → ℝ) (hx : seq_bounded x) :
  ∃ m, minimum {l | ∃ (a : ℕ → ℕ), extraction a ∧ seq_is_limit (x ∘ a) l} m
  ∧ ∃ M, maximum {l | ∃ (a : ℕ → ℕ), extraction a ∧ seq_is_limit (x ∘ a) l} M := by
  set L := {l | ∃ (a : ℕ → ℕ), extraction a ∧ seq_is_limit (x ∘ a) l} -- getting our alias
  have hneL : Nonempty L := by
    simp  -- simplify the goal
    obtain ⟨a, ha, l, hl⟩ := subseq_BolzanoWeierstrass' x hx  -- get the limit and subsequence
    use l, a  -- use the necessary extraction and limit

  have hL : bounded L := by
    -- obtain ⟨l, hL⟩ := hneL
    constructor
    .

      suffices h : ∀ (a : ℕ → ℕ), extraction a ∧ seq_bound_above (x ∘ a) from by
        /-

        -/
        have := seq_bound_imp_subseq_bound x
        simp_all only [true_and, Set.coe_setOf, nonempty_subtype, forall_const, L]
        obtain ⟨w, h_1⟩ := hneL
        obtain ⟨w_1, h_1⟩ := h_1
        use w
        simp
        intro l a ha
        sorry




      stop
      use C
      simp only [Set.mem_setOf_eq, ge_iff_le, forall_exists_index, and_imp]
      intro x₀ hx₀

      apply seq_bound_imp_subseq_bound x a ha

      specialize hC x₀
      simp at hC
      specialize hC (a 1)
      generalize 1 = n at *

      sorry
    .
      obtain ⟨c, hc⟩ := hx.right
      sorry

  sorry

lemma sup_eq_neg_inf (X : Set ℝ) [Nonempty X] (hx : bound_above X) : ∃ C, infimum (-X) (-C) ∧ supremum X C := by
  let S := {-x | x ∈ X}
  have := completeness_axiom X hx
  rename_i inst
  obtain ⟨C, hC⟩ := this
  use C
  simp [hC]
  have : (-X) = S := by
    ext x
    constructor
    . intro h
      simp_all
      dsimp [S]
      use (-x)
      simp [h]
    .
      intro h
      dsimp [S] at h
      obtain ⟨a, ha, h1⟩ := h
      rw [←h1]
      simp [ha]
  rw [this]

  obtain ⟨a, ha⟩ := inst
  intro hB B h1
  specialize h1 (-a)
  specialize hB (-a)
  rw [←Set.mem_neg, ←this, neg_neg] at h1 hB
  simp [ha] at h1 hB
  rw [le_neg] at h1
  sorry

/-- Given a bounded sequence `x : ℕ → ℝ`, define `seq_sup` as the sequence of supremums of the tail sets. -/
noncomputable
def seq_sup (x : ℕ → ℝ) (hx : seq_bounded x) : ℕ → ℝ := fun n =>
  let S := {xm | ∃ m : ℕ, m ≥ n ∧ xm = x m}
  have S_id : S = {xm | ∃ m : ℕ, m ≥ n ∧ xm = x m} := by rfl

  have hS1 : bound_above S := by
    dsimp [bound_above]
    obtain ⟨h1, h2⟩ := hx
    obtain ⟨C, hc⟩ := h1
    use C
    intro xm
    specialize hc xm
    have : xm ∈ S → xm ∈ {x_1 | ∃ n, x n = x_1} := by simp_all
    intro h
    apply this at h
    apply hc at h
    exact h

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

example : seq_bounded (fun n => (-1) ^ n) := by
  dsimp [seq_bounded, bounded]
  have h1 : ∀ (n : ℕ), |(-1 : ℝ) ^ n| ≤ 1 := by simp
  conv at h1 =>
    ext n
    rw [abs_le']
    rw [neg_le]

  constructor
  .
    use 1
    simp
    intro a
    apply (h1 a).left
  .
    use -1
    simp
    intro n
    apply (h1 n).right

lemma le_tric (a b : ℝ) : a ≤ b ∧ b ≤ a → a = b := by
  simp
  intro h1 h2
  by_contra h
  push_neg at h
  rw [le_iff_lt_or_eq] at *
  obtain h1a | h1b := h1
  obtain h2a | h2b := h2
  linarith
  repeat' tauto


lemma seq_bound_iff_bounds (x : ℕ → ℝ) : seq_bounded x ↔ ∃ (c C : ℝ), ∀ (n : ℕ), c ≤ x n ∧ x n ≤ C := by
  constructor
  .
    intro hx
    obtain ⟨C, hC⟩ := hx.left -- getting upper bound
    obtain ⟨c, hc⟩ := hx.right  -- getting lower bound
    use c, C
    intro n
    specialize_all (x n)
    simp at *
    simp [hc, hC]
  .
    intro hx
    obtain ⟨c, C, hc⟩ := hx
    dsimp [seq_bounded, bounded]
    constructor
    .
      use C
      simp [hc]
    .
      use c
      simp [hc]



lemma seq_bound_iff_bounds' (x : ℕ → ℝ) (h1 : ¬(∃ (a : ℝ), ∀ n, x n = a)) : seq_bounded x ↔ ∃ (c C : ℝ), c < C ∧ ∀ (n : ℕ), c ≤ x n ∧ x n ≤ C := by
  push_neg at h1
  constructor
  .
    intro hx
    obtain ⟨C, hC⟩ := hx.left -- getting upper bound
    obtain ⟨c, hc⟩ := hx.right  -- getting lower bound
    use c, C  -- setting the upper and lower bounds
    constructor
    . -- showing c < C
      rw [lt_iff_le_and_ne]
      constructor
      .
        simp_all  -- simplify
        specialize_all (0 : ℕ)  -- specialize to any natural
        linarith  -- linearity does the rest
      .
        simp_all
        specialize h1 C
        obtain ⟨n, hn⟩ := h1
        push_neg at *
        specialize hc n
        specialize hC n
        by_contra h
        rw [h] at hc
        rw [le_iff_lt_or_eq] at hc
        obtain ha1 | ha2 := hc
        . linarith
        . tauto
    simp at *
    simp [hc, hC]
  .
    intro hx
    obtain ⟨c, C, hc⟩ := hx
    dsimp [seq_bounded, bounded]
    constructor
    .
      use C
      simp [hc]
    .
      use c
      simp [hc]

example : seq_bounded (fun (n : ℕ) => (1 : ℝ)) := by
  rw [seq_bound_iff_bounds]
  use 1, 1
  simp

lemma seq_infseq_inc (x : ℕ → ℝ) (hx : seq_bounded x) : seq_mono_inc (seq_inf x hx) ∧ seq_bounded (seq_inf x hx) := by
  have h1 : ∃ (c C : ℝ), c ≤ C ∧ ∀ n, (c ≤ x n ∧ x n ≤ C) := by
    rw [seq_bound_iff_bounds] at hx
    obtain ⟨c, C, hC⟩ := hx
    use c, C
    constructor
    . specialize hC 1 -- specialise to any number
      generalize 1 = n at hC  -- generalise this to any natural
      linarith  -- linearity takes care of the rest
    . exact hC

  let ix := seq_inf x hx
  have : ix = seq_inf x hx := by rfl
  rw [←this]
  clear this

  constructor
  .
    intro n m hnm
    dsimp [ix]

    sorry
  .

    obtain ⟨C, hC⟩ := hx
    use C
    intro n hCn
    simp at *
    obtain ⟨n1, hn1⟩ := hCn
    specialize hC n
    simp at hC



    sorry

lemma seq_supseq_dec (x : ℕ → ℝ) (hx : seq_bounded x) : seq_mono_dec (seq_sup x hx) ∧ seq_bounded (seq_sup x hx) := by
  sorry

lemma seq_infseq_le_supseq (x : ℕ → ℝ) (hx : seq_bounded x) :
  (seq_mono_dec (seq_sup x hx) ∧ seq_bounded (seq_sup x hx)) ∧
  (seq_mono_inc (seq_inf x hx) ∧ seq_bounded (seq_inf x hx)) := by
  stop
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
  stop
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
-/
