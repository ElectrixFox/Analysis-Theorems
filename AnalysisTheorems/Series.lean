import AnalysisTheorems.Sequences


open BigOperators

open Finset

def seq_partial_sums (a : ℕ → ℝ) : ℕ → ℝ :=
  fun n => (∑ i ∈ Icc 0 n, a i)

lemma sum_add (a : ℕ → ℝ) {n : ℕ} : ∑ i ∈ Icc 0 (n + 1), a i = (∑ i ∈ Icc 0 n, a i) + a (n + 1) := by
  simp [sum_Icc_succ_top]

def sum_is_limit (x : ℕ → ℝ) (l : ℝ) : Prop :=
  seq_is_limit (seq_partial_sums x) l

def sum_is_limit' (a : ℕ → ℝ) (l : ℝ) (N : ℕ) : Prop :=
  sum_is_limit a (l - (∑ i ∈ Icc 0 (N - 1), a i))

def seq_partial_sums' (a : ℕ → ℝ) (N : ℕ := 1) : ℕ → ℝ :=
  fun n => (∑ i ∈ Icc N n, a i)

lemma sum_tail_conv (x : ℕ → ℝ) (n0 : ℕ) : (∃ l, sum_is_limit x l) ↔ (∃ m, sum_is_limit' x m n0) := by
  constructor
  .
    intro hl
    obtain ⟨l, hx⟩ := hl
    dsimp [sum_is_limit']
    set m := ∑ i ∈ Icc 0 (n0 - 1), x i
    use (l + m)
    simp
    rw [sum_is_limit] at hx
    apply hx
  .
    intro hx'
    obtain ⟨m, hm⟩ := hx'
    dsimp [sum_is_limit'] at hm
    set l := ∑ i ∈ Icc 0 (n0 - 1), x i
    use (m - l)

lemma seq_convto_general (x : ℕ → ℝ) (l : ℝ) (hx : seq_is_limit x l) (s : ℕ) : seq_is_limit (fun n => x (n + s)) l := by
  -- get all the usual stuff
  intro ε hε
  specialize hx ε hε
  obtain ⟨N, hN⟩ := hx
  use N
  intro n hn
  specialize hN (n + s) -- show it must be true for n + s ≥ N
  apply hN  -- apply this
  linarith  -- linearity shows us this is true

lemma seq_convto_general_iff (x : ℕ → ℝ) (l : ℝ) : seq_is_limit x l ↔ ∀ (s : ℕ), seq_is_limit (fun n => x (n + s)) l := by
  constructor
  . apply seq_convto_general  -- sorting the forward case
  . -- the backward case
    intro hx
    specialize hx 0
    simp at hx
    apply hx

lemma seq_convto_general_iff' (x : ℕ → ℝ) (l : ℝ) (s : ℕ) : seq_is_limit x l ↔ seq_is_limit (fun n => x (n + s)) l := by
  constructor
  . intro h
    apply seq_convto_general x l h  -- sorting the forward case
  . -- the backward case
    intro hs
    intro ε hε
    specialize hs ε hε
    obtain ⟨N, hN⟩ := hs
    use (N + s)
    simp at hN
    intro n hn
    specialize hN (n - s) (by omega)
    suffices (x (n - s + s) = x n) by
      rw [←this]
      apply hN
    suffices ((n - s + s) = n) by
      rw [this]
    omega


lemma sum_conv_if_seq_convto_zero (a : ℕ → ℝ) : (∃ l, sum_is_limit a l) → seq_is_limit a 0 := by
  dsimp [sum_is_limit]
  intro h
  obtain ⟨l, hl⟩ := h
  set s : ℕ → ℝ := seq_partial_sums a

  have h1 : ∀ k, a (k + 1) = s (k + 1) - s k := by
    intro k
    dsimp [s, seq_partial_sums]
    simp [sum_add]

  have h2 : seq_is_limit (fun n => a (n + 1)) 0 := by
    conv_lhs => ext n; apply h1
    have := seq_COLT_scalarmult s l hl (-1) -- getting the first colt
    simp at this
    conv_lhs => ext n; rw [sub_eq_add_neg]
    conv_rhs => rw [←sub_self l, sub_eq_add_neg]
    apply seq_COLT_addition _ _ l (-l) (by apply seq_convto_general s l hl) this

  rw [seq_convto_general_iff' a 0 1]  -- sorting out the limit
  apply h2

theorem sum_COLT_add (a b : ℕ → ℝ) (l m : ℝ) (ha : sum_is_limit a l) (hb : sum_is_limit b m) : sum_is_limit (fun k => a k + b k) (l + m) := by
  unfold sum_is_limit seq_partial_sums at * -- unfold the definitions
  conv_lhs => ext n; simp [sum_add_distrib] -- do some manipulations
  exact seq_COLT_addition _ _ _ _ ha hb -- apply normal COLT

theorem sum_COLT_scalarmult (a : ℕ → ℝ) (l : ℝ) (c : ℝ) (ha : sum_is_limit a l) : sum_is_limit (fun k => c * a k) (c * l) := by
  unfold sum_is_limit seq_partial_sums at * -- unfold the definitions
  conv_lhs =>
    ext n
    simp
    conv => rhs; ext x; rw [mul_comm]
    rw [←sum_mul, mul_comm]

  -- do some conversions to show what we need
  conv_lhs => ext n; rw [show ((c * ∑ i ∈ Icc 0 n, a i) = c * (∑ i ∈ Icc 0 n, a i)) by rfl]
  exact seq_COLT_scalarmult _ _ ha _ -- apply normal COLT
