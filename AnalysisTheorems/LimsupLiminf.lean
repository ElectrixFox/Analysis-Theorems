import AnalysisTheorems.Subsequences

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
