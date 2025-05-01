import AnalysisTheorems.Subsequences

lemma bound_bel (X : Set ℝ) [Nonempty X] : bound_below X → ∃ c, infimum X c := by
  sorry

noncomputable
def supseq (x : ℕ → ℝ) (hb : seq_bounded x) : ℕ → ℝ := fun n =>
  let S : Set ℝ := {x m | m ≥ n}
  have hS1 : Nonempty S := by simp [Set.Nonempty.of_subtype, S]; tauto
  have hS2 : bound_above S := by
    obtain ⟨B, hB⟩ := hb.left
    use B
    intro xi hxi
    obtain ⟨m, ⟨hm1, hm2⟩⟩ := hxi
    rw [←hm2]
    tauto

  (completeness_axiom S hS2).choose

noncomputable
def infseq (x : ℕ → ℝ) (hb : seq_bounded x) : ℕ → ℝ := fun n =>
  let S : Set ℝ := {x m | m ≥ n}
  have hS1 : Nonempty S := by simp [Set.Nonempty.of_subtype, S]; tauto
  have hS2 : bound_below S := by
    obtain ⟨B, hB⟩ := hb.right
    use B
    intro xi hxi
    obtain ⟨m, ⟨hm1, hm2⟩⟩ := hxi
    rw [←hm2]
    tauto

  (bound_bel S hS2).choose

lemma boundseqmono (x : ℕ → ℝ) (hx : seq_bounded x) (hx1 : ∀ n m, n ≠ m → x n ≠ x m) : seq_mono_dec (supseq x hx) ∧ seq_bounded (supseq x hx) := by
  set a := (supseq x hx)
  set b := (infseq x hx)
  have hx0 := hx
  obtain ⟨⟨C, hC⟩, ⟨c, hc⟩⟩ := hx0
  have h : c < C := by
    specialize hc (x 0) (by simp)
    specialize hC (x 0) (by simp)
    have := calc
      c ≤ x 0 := hc
      _ ≤ C := hC
    sorry
  have h2 : ∀ n, x n ∈ Set.Icc c C := by
    intro n
    constructor
    . specialize hc (x n) (by simp)
      exact hc
    . specialize hC (x n) (by simp)
      exact hC

  let X : ℕ → Set ℝ := fun n => {x m | m ≥ n}

  have h12 : ∀ n, (X n) ⊆ Set.Icc c C := by
    intro n p hp
    dsimp [X] at hp
    constructor
    . obtain ⟨m, ⟨hm1, hm2⟩⟩ := hp
      specialize hc (x m) (by simp)
      rw [hm2] at hc
      exact hc
    . obtain ⟨m, ⟨hm1, hm2⟩⟩ := hp
      specialize hC (x m) (by simp)
      rw [hm2] at hC
      exact hC

  have h3 : ∀ n, ∀ p ∈ X n, c ≤ p ∧ p ≤ C := by
    intro n p hp
    simp at hp
    constructor
    .
      rw [Set.mem_setOf_eq] at hp
      obtain ⟨m, ⟨hp1, hp2⟩⟩ := hp
      rw [←hp2]
      specialize hc (x m) (by simp)
      apply hc
    .
      rw [Set.mem_setOf_eq] at hp
      obtain ⟨m, ⟨hp1, hp2⟩⟩ := hp
      rw [←hp2]
      specialize hC (x m) (by simp)
      apply hC

  have h11 : ∀ n, ∃ w, supremum (X n) w := by
    intro n
    have hXne : Nonempty (X n) := by sorry
    have hXb : bounded (X n):= by
      constructor
      use C
      apply (h12 n)

    apply completeness_axiom (X n) hXb.left


  have h4 : ∀ (n : ℕ), c ≤ b n ∧ a n ≤ C := by
    intro n
    constructor
    .
      sorry
    .

      sorry

  have h5 : seq_bounded b := by sorry
  have h6 : seq_bounded a := by sorry
  constructor
  .
    intro m n hm1
    have h7 : X n ⊆ X m := by sorry
    have h8 : ∃ o, ((∀ p ∈ (X m), p ≤ o) → (∀ q ∈ (X n), q ≤ o)) := by sorry
    have h10 : bound_above (X m) := by sorry

    have h9 : bound_above (X n) := by
      rw [Set.subset_def] at h7
      apply subset_bound_bounded (X m) h10 (X n) h7

    have : a m ≥ a n := by
      obtain ⟨hX1, hX2⟩ := h9
      obtain ⟨o, h8⟩ := h8

      sorry


    rw [ge_iff_le] at this
    apply this
  . exact h6

/-
lemma seq_conv_bound_above_sub_bound_above (x : ℕ → ℝ) (a : ℕ → ℕ) (ha : extraction a) : seq_bound_above x → seq_bound_above (x ∘ a) := by
  intro h
  obtain ⟨C, hC⟩ := h
  use C
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
    have h1 := subseq_BolzanoWeierstrass' x hx
    have h2 := seq_bound_imp_subseq_bound x
    have h3 := conv_seq_is_bounded x
    have h4 := seq_conv_bound_above_sub_bound_above x
    obtain ⟨⟨c, hc⟩, ⟨C, hC⟩⟩ := hx
    dsimp [bounded]
    constructor
    .
      dsimp [L]
      use C
      intro l hl
      simp at hl
      obtain ⟨a, ha, hl⟩ := hl
      apply conv_seq_bound_above_imp_lim_bound_above (x ∘ a) l
      . apply hl
      .
        intro n
        simp
        apply conv_seq_is_bounded at hl
        obtain ⟨p, hp⟩ := hl
        simp at hp
        specialize hp n
        sorry


    sorry
  sorry

-/
