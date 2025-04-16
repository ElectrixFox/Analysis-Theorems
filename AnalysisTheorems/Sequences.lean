import AnalysisTheorems.Sets

lemma lt_add_imp_le (a b : ℝ) : (∀ ε > 0, a < b + ε) → a ≤ b := by
  intro h
  by_contra h1  -- assume a > b
  push_neg at h1
  rw [show b < a ↔ b - a < 0 by simp] at h1 -- show b - a < 0
  specialize h (a - b)  -- so use ε = a - b
  simp at h -- then this says b < a and a ≤ b which is clearly a contradiction
  linarith

lemma abs_sub_le_add (a b c : ℝ) : |a - b| < c → |a| ≤ |b| + c := by
  intro h
  have h1 := calc
      |a| = |a - b + b| := by simp
      _ ≤ |a - b| + |b| := by apply abs_add
  linarith

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

def seq_bound_above (a : ℕ → ℝ) : Prop := bound_above {a n | n : ℕ}

def seq_bound_below (a : ℕ → ℝ) : Prop := bound_below {a n | n : ℕ}

def seq_bounded (a : ℕ → ℝ) : Prop := bounded {a n | n : ℕ}

lemma conv_seq_bound_below_imp_lim_bound_below (x : ℕ → ℝ) (l : ℝ) (hx : seq_is_limit x l) (a : ℝ) : (∀ n, x n ≥ a) → l ≥ a := by
  dsimp [seq_is_limit] at hx
  intro h

  conv at hx =>
    intro ε hε  -- let ε > 0
    rhs
    ext N -- exists an N
    intro n hn  -- for any n ≥ N
    rw [abs_lt]
    rw [lt_sub_iff_add_lt, add_comm, ←sub_eq_add_neg]
    rhs
    rw [sub_eq_add_neg, ←lt_sub_iff_add_lt, sub_neg_eq_add, add_comm]
    -- l - ε < x n < l + ε

  have h1 : ∀ ε > 0, a < l + ε := by
    intro ε hε
    specialize hx ε hε  -- apply this to the limit definition
    obtain ⟨N, hN⟩ := hx  -- get our N
    specialize hN N -- use our N as the starting point
    simp at hN  -- get the inequality on its own
    specialize h N  -- now use x n ≥ a for all n
    linarith

  apply lt_add_imp_le
  exact h1

theorem conv_seq_is_bounded (xn : ℕ → ℝ) (x : ℝ) (hx : seq_is_limit xn x) : seq_bound_above xn := by
  specialize hx 1
  simp at hx
  obtain ⟨N, hN⟩ := hx
  have h1 : ∀ n ≥ N, |xn n| ≤ |xn n - x| + |x| ∧ |xn n - x| + |x| ≤ |x| + 1 := by
    intro n hn
    specialize hN n hn
    constructor
    .
      calc
        |xn n| = |xn n - x + x| := by ring_nf
        _ ≤ |xn n - x| + |x| := by apply abs_add_le
    . linarith [hN]

  have h2 : ∀ n ≥ N, |xn n - x| + |x| ≤ |x| + 1 := by
    intro n hn
    specialize hN n hn
    linarith

  let C := |x| + 1
  let B := max (|xn 1|) (|x| + 1)
  have h3 : ∀ n : ℕ, |xn n| ≤ B := by
    intro n
    dsimp [B]
    simp
    sorry

  use B
  intro m hm
  simp at hm
  simp
  obtain ⟨n, hn⟩ := hm
  specialize h3 n
  rw [←hn]
  rw [abs_le] at h3
  apply h3.right

theorem conv_seq_is_bounded' (xn : ℕ → ℝ) (x : ℝ) (hx : seq_is_limit xn x) : seq_bounded xn := by
  have h0 := hx
  specialize hx 1
  simp at hx
  obtain ⟨N, hN⟩ := hx
  have h1 : ∀ n ≥ N, |xn n| ≤ |xn n - x| + |x| ∧ |xn n - x| + |x| ≤ |x| + 1 := by
    intro n hn
    specialize hN n hn
    constructor
    .
      calc
        |xn n| = |xn n - x + x| := by ring_nf
        _ ≤ |xn n - x| + |x| := by apply abs_add_le
    . linarith [hN]

  have h2 : ∀ n ≥ N, |xn n - x| + |x| ≤ |x| + 1 := by
    intro n hn
    specialize hN n hn
    linarith

  let C := |x| + 1
  let s : Finset ℝ := (Finset.range (N + 1)).image (fun n => |xn n|)  -- getting the set x_1, ..., x_(N - 1)
  let P : ℝ := s.max' (by simp [s])
  let B := max P (|x| + 1)
  have : ∀ n, |xn n| ≤ B := by
    intro n
    by_cases hn : n < N
    .

      sorry
    . sorry

  constructor
  . use B
    intro lx hln
    simp at hln
    obtain ⟨n, hn⟩ := hln
    rw [←hn]
    simp
    specialize this n
    apply abs_le_imp_le
    exact this
  .
    use -B
    intro lx hln
    simp at hln
    obtain ⟨n, hn⟩ := hln
    rw [←hn]
    specialize this n
    rw [abs_le] at this
    apply this.left

theorem seq_squeeze_zero (x : ℕ → ℝ) (y : ℕ → ℝ) (hy : seq_is_limit y 0) (hxy : ∀ (n : ℕ), |x n| ≤ y n) : seq_is_limit x 0 := by
  sorry

lemma seq_COLT_linearity (xn : ℕ → ℝ) (yn : ℕ → ℝ) (x y : ℝ) (hx : seq_is_limit xn x) (hy : seq_is_limit yn y) (a b : ℝ) : seq_is_limit (fun (n : ℕ) => a * (xn n) + b * (yn n)) (a * x + b * y) := by
  sorry

lemma seq_COLT_mult (xn : ℕ → ℝ) (yn : ℕ → ℝ) (x y : ℝ) (hx : seq_is_limit xn x) (hy : seq_is_limit yn y) : seq_is_limit (fun (n : ℕ) => (xn n) * (yn n)) (x * y) := by
  sorry

lemma seq_COLT_ratio (xn : ℕ → ℝ) (yn : ℕ → ℝ) (x y : ℝ) (hx : seq_is_limit xn x) (hy : seq_is_limit yn y) (hy1 : y ≠ 0) (hy2 : ∀ (n : ℕ), yn n ≠ 0): seq_is_limit (fun (n : ℕ) => (xn n) / (yn n)) (x / y) := by
  sorry


theorem seq_COLT_scalarmult (x : ℕ → ℝ) (l : ℝ) (hx : seq_is_limit x l) (a : ℝ) : seq_is_limit (fun n => a * x n) (a * l) := by
  have := seq_COLT_linearity x (fun n => 0) l 0 hx (by simp_all [seq_is_limit]) a 0
  simp at this
  exact this

lemma conv_seq_bound_above_imp_lim_bound_above (x : ℕ → ℝ) (l : ℝ) (hx : seq_is_limit x l) (b : ℝ) : (∀ n, x n ≤ b) → l ≤ b := by
  intro h
  have h1 := seq_COLT_scalarmult x l hx (-1)
  simp at h1

  conv at h =>
    intro n
    rw [←neg_le_neg_iff]

  rw [←neg_le_neg_iff]
  apply conv_seq_bound_below_imp_lim_bound_below (fun n => -x n) _ (by simp_all)
  simp_all

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
