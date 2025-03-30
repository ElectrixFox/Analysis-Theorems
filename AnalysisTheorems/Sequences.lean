import AnalysisTheorems.Sets

def seq_is_limit (x : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - l| < ε

theorem seq_uniquelim (x : ℕ → ℝ) (l m : ℝ) (h1 : seq_is_limit x l) (h2 : seq_is_limit x m) : l = m := by
  by_contra h3
  have : |l - m| > 0 := by
    apply lt_of_le_of_ne
    . apply abs_nonneg
    intro ha
    symm at ha
    rw [abs_eq_zero, sub_eq_zero] at ha
    tauto
  let ε := |l - m| / 2
  have hε : ε > 0 := by dsimp [ε]; linarith

  rcases h1 ε hε with ⟨N₁, hN₁⟩
  rcases h2 ε hε with ⟨N₂, hN₂⟩
  let N := max N₁ N₂
  have h4 : |x N - l| < ε := by
    apply hN₁
    apply le_max_left

  have h5 : |x N - m| < ε := by
    apply hN₂
    apply le_max_right

  have : |l - m| < 2 * ε := by
    calc
      |l - m| = |(l - x N) + (x N - m)| := by simp
      _ ≤ |l - x N| + |x N - m| := by apply abs_add_le
      _ < ε + ε := by rw [abs_sub_comm] at h4; gcongr
      _ = 2 * ε := by ring_nf

  dsimp [ε] at this
  ring_nf at this
  linarith

def seq_bound_above (a : ℕ → ℝ) : Prop :=
  bound_above {a n | n : ℕ}

def seq_bound_below (a : ℕ → ℝ) : Prop :=
  bound_below {a n | n : ℕ}

def seq_bounded (a : ℕ → ℝ) : Prop :=
  bound_above {|a n| | n : ℕ}

theorem conv_seq_is_bounded (xn : ℕ → ℝ) (x : ℝ) (hx : seq_is_limit xn x) : seq_bound_above xn := by
  specialize hx 1
  simp at hx
  obtain ⟨N, hN⟩ := hx
  have h1 : ∀ n ≥ N, |xn n| ≤ |xn n - x| := by
    intro n hn
    specialize hN n hn
    sorry

  have h2 : ∀ n ≥ N, |xn n - x| + |x| ≤ |x| + 1 := by
    intro n hn
    specialize hN n hn
    linarith

  let C := |x| + 1
  let B := max (|xn 1|) (|x| + 1)
  have h3 : ∀ n : ℕ, |xn n| ≤ B := by sorry

  use B
  intro m hm
  simp at hm
  simp
  obtain ⟨n, hn⟩ := hm
  specialize h3 n
  rw [←hn]
  rw [abs_le] at h3
  apply h3.right

theorem seq_squeeze_zero (x : ℕ → ℝ) (y : ℕ → ℝ) (hy : seq_is_limit y 0) (hxy : ∀ (n : ℕ), |x n| ≤ y n) : seq_is_limit x 0 := by
  sorry

lemma seq_COLT_linearity (xn : ℕ → ℝ) (yn : ℕ → ℝ) (x y : ℝ) (hx : seq_is_limit xn x) (hy : seq_is_limit yn y) (a b : ℝ) : seq_is_limit (fun (n : ℕ) => a * (xn n) + b * (yn n)) (a * x + b * y) := by
  sorry

lemma seq_COLT_mult (xn : ℕ → ℝ) (yn : ℕ → ℝ) (x y : ℝ) (hx : seq_is_limit xn x) (hy : seq_is_limit yn y) : seq_is_limit (fun (n : ℕ) => (xn n) * (yn n)) (x * y) := by
  sorry

lemma seq_COLT_ratio (xn : ℕ → ℝ) (yn : ℕ → ℝ) (x y : ℝ) (hx : seq_is_limit xn x) (hy : seq_is_limit yn y) (hy1 : y ≠ 0) (hy2 : ∀ (n : ℕ), yn n ≠ 0): seq_is_limit (fun (n : ℕ) => (xn n) / (yn n)) (x / y) := by
  sorry

theorem seq_limininterval (xn : ℕ → ℝ) (x : ℝ) (a b : ℝ) (X : Set ℝ) (hX : X = {x : ℝ | a ≤ x ∧ x ≤ b}) (xnI : ∀ (n : ℕ), (xn n) ∈ X) : seq_is_limit xn x → x ∈ X := by
  sorry

lemma seq_limineq (xn yn : ℕ → ℝ) (x y : ℝ) (hx : seq_is_limit xn x) (hy : seq_is_limit yn y) (hxy : ∀ (n : ℕ), xn n ≤ yn n) : x ≤ y := by
  sorry

theorem seq_sqrtcont (xn : ℕ → ℝ) (x : ℝ) (hx : seq_is_limit xn x) (hx1 : ∀ (n : ℕ), xn n ≥ 0) : seq_is_limit (fun (n : ℕ) => √(xn n)) (√(x)) := by
sorry

/- Monotone increasing sequence for type ℕ → α -/
def seq_mono_inc {α : Type} [LE α] (x : ℕ → α) : Prop := ∀ (m n : ℕ), m ≤ n → x m ≤ x n

/- Monotone decreasing sequence for type ℕ → α -/
def seq_mono_dec {α : Type} [LE α] (x : ℕ → α) : Prop := ∀ (m n : ℕ), m ≥ n → x m ≥ x n

theorem seq_boundmonoinc_conv (x : ℕ → ℝ) (l : ℝ) (hx : seq_mono_inc x) : seq_is_limit x l := by
  sorry

/- If x is bounded and monotonically increasing or decreasing then it converges -/
theorem seq_mono_bound_conv (x : ℕ → ℝ) (hx : seq_bounded x) : seq_mono_inc x ∨ seq_mono_dec x → ∃ l, seq_is_limit x l := by
  sorry

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

def seq_dec (x : ℕ → ℝ) : Prop := ∀ n, x (n + 1) ≤ x n

def subseq (a : ℕ → ℕ) : Prop := ∀ (n m : ℕ), n < m → a n < a m

def subseq_bijection (x : ℕ → ℝ) (a : ℕ → ℕ) (ha : subseq a) : ℕ → ℝ := x ∘ a

def even_subs (a : ℕ → ℝ) : ℕ → ℝ := a ∘ (fun n ↦ 2 * n)

def even_subs' (a : ℕ → ℝ) : ℕ → ℝ := a ∘ eseq where
  eseq := (fun n ↦ 2 * n)
  h := subseq eseq

lemma seq_bound_imp_subseq_bound (x : ℕ → ℝ) (a : ℕ → ℕ) (ha : subseq a) : seq_bounded x → seq_bounded (x ∘ a) := by
  intro h
  dsimp [seq_bounded, bound_above] at * -- simplify the definitions
  simp_all  -- simplify further
  obtain ⟨c, h⟩ := h  -- get our upper bound from the hypothesis
  use c -- use this upper bound
  intro j -- get the new variable
  apply h -- apply the hypothesis

lemma subseq_ge_index (a : ℕ → ℕ) (ha : subseq a) : ∀ j, a j ≥ j := by
  sorry

lemma subseq_conv_to_seq_limit {b : ℕ → ℝ} (l : ℝ) (x : ℕ → ℝ) (a : ℕ → ℕ) (hx : seq_is_limit x l)
  (ha : subseq a) (hb : b = subseq_bijection x a ha) : seq_is_limit b l := by
  intro ε hε
  specialize hx ε hε
  obtain ⟨N, hN⟩ := hx
  use N -- use the N from the main sequence
  intro n hn
  specialize hN (a n)

  have h1 : a n ≥ N := by
    have := subseq_ge_index a -- get the general fact
    apply this at ha  -- apply the a j ≥ j
    specialize ha n -- specialize this to n so a n ≥ n
    linarith  -- linearity does the rest

  dsimp [subseq_bijection] at hb
  simp [hb]
  exact hN h1

lemma seq_contsub_inc_or_dec (x : ℕ → ℝ) : ∃ a : ℕ → ℕ, subseq a ∧ (seq_mono_inc (x ∘ a) ∨ seq_mono_dec (x ∘ a)) := by
  let P := {n0 : ℕ | ∀ n > n0, x n0 ≥ x n}  -- the set of "peak" indices

  by_cases h : P.Finite
  .
    dsimp [Set.Finite] at h
    aesop
    have h1 : ∃ (n1 : ℕ), ∀ n ∈ P, n < n1 := by
      sorry

    let n0 := h1.choose
    have h2 (n1 : ℕ) : ∃ (n2 : ℕ), n2 > n1 ∧ x n1 < x n2 := by
      sorry

    let an : ℕ → ℕ
      | 0 => n0
      | .succ n => (h2 n).choose

    have han1 : subseq an := by
      sorry

    use an
    constructor
    . apply han1
    .
      constructor
      dsimp [seq_mono_inc]
      intro m n hn
      dsimp [an]
      sorry



  .
    dsimp [Set.Finite] at h
    aesop

    sorry

theorem subseq_BolzanoWeierstrass (x : ℕ → ℝ) (hx : seq_bounded x) : ∃ a, subseq a → ∃ l, seq_is_limit (x ∘ a) l := by
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
        . sorry
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
      have hle := completeness_axiom_subset Sm Sn hSm hSn hsub
      exact hle
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
      exact (completeness_axiom Sn hSn).choose_spec.left
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
        . linarith
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
      have hle := completeness_axiom_subset (-Sn) (-Sm) (set_bound_above_neg_bound_below Sn hSn) (set_bound_above_neg_bound_below Sm hSm) (fun x hx => hsub (-x) hx)
      simp at hle
      exact hle
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
      exact (completeness_axiom (-Sn) (set_bound_above_neg_bound_below Sn hSn)).choose_spec.left.neg
  constructor
  .
    constructor
    . sorry
    . sorry
  .
    constructor
    . sorry
    . sorry


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
