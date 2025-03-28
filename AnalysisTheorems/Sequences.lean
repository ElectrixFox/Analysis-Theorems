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
  sorry

theorem subseq_BolzanoWeierstrass (x : ℕ → ℝ) (hx : seq_bounded x) : ∃ a, subseq a → ∃ l, seq_is_limit (x ∘ a) l := by
  have := seq_contsub_inc_or_dec x
  obtain ⟨a, ha⟩ := this
  use a
  intro h1
  simp [h1] at ha
  obtain ha1 | ha2 := ha
  .
    apply seq_mono_bound_conv (x ∘ a)
    .
      dsimp [seq_bounded, bound_above] at * -- simplify definitions
      simp_all  -- simplify everything down further
      use hx.choose -- get the c from the bounded
      intro a1  -- get our x
      apply hx.choose_spec  -- show that since the sequence is bounded so is the subseq
    .
      tauto -- show that it is true by True ∨ something is always true
      /-
      dsimp [seq_bounded, bound_above]
      dsimp [seq_bounded, bound_above] at hx
      simp_all
      obtain ⟨c, h⟩ := hx
      use c
      intro a1
      apply h
      -/

  sorry
