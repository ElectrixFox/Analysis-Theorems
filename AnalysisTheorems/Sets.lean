import Mathlib

-- def bound_above (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≥ x
def bound_below (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≤ x

def bound_above (X : Set ℝ) : Prop := ∃ (c : ℝ), ∀ x, x ∈ X → c ≥ x
def bound_above_by (X : Set ℝ) (c : ℝ) : Prop := ∀ x, x ∈ X → c ≥ x

-- def bound_above_by (X : Set ℝ) (c : ℝ) : Prop := bound_above X → ∀ x, x ∈ X → x ≤ c
def bound_below_by (X : Set ℝ) (c : ℝ) : Prop := bound_below X → ∀ x, x ∈ X → c ≤ x

-- def supremum (X : Set ℝ) (C : ℝ) := bound_above_by X C → (∀ (B : ℝ), (bound_above_by X B) → (C ≤ B))
def supremum (X : Set ℝ) (C : ℝ) := (∀ x ∈ X, x ≤ C) ∧ (∀ B, (∀ x ∈ X, x ≤ B) → C ≤ B)

def infimum (X : Set ℝ) := bound_below X → ∃ (C : ℝ), ∀ (B : ℝ), (bound_below_by X C) ∧ (bound_below_by X B) ∧ (C ≤ B)

example (X : Set ℝ) (hX : X = {x : ℝ | x < 2}) : bound_above_by X 2 := by
  intro x hx
  generalize hc : (2 : ℝ) = c
  rw [hX] at hx
  rw [Set.mem_setOf] at hx
  linarith

example (X : Set ℝ) (hX : X = {x : ℝ | x < 2}) : supremum X 2 := by
  rw [hX]
  constructor
  . 
    intro x hx
    exact le_of_lt hx
  . 
    intro B hB
    apply le_of_not_lt
    intro hbl
    let x := (B + 2) / 2
    have hxin : x ∈ {x : ℝ | x < 2} := by
      subst hX
      simp
      calc
        x = (B + 2) / 2 := by rfl
        _ < (2 + 2) / 2 := by linarith
        _ = 2 := by norm_num
    have : x ≤ B := hB x hxin
    simp at hxin
    specialize hB x
    simp at hB
    contrapose hB
    simp at hB
    simp
    constructor
    linarith
    simp [x]
    linarith

axiom completeness_axiom {X : Set ℝ} [Nonempty X] : bound_above X → ∃ C, supremum X C

theorem archimedes (a b : ℝ) (hb : b > 0) : ∃ (n : ℕ), n * b > a := by
  by_contra h
  simp at h
  let X : Set ℝ := {n * b | n : ℕ}  -- define the set
  have hXn : Nonempty X := by -- nonempty
    simp  -- simplify to there is an a in X
    use b -- b is naturally in X
    dsimp [X]
    use 1 -- 1 * b = b
    simp  -- simplification

  have hXb : bound_above X := by  -- it is obviously bounded above by a
    use a
    simp
    dsimp [X]
    intro x hx
    obtain ⟨n, hn⟩ := hx
    subst hn
    apply h

  have hXsup : ∃ C, supremum X C := completeness_axiom hXb  -- by the completeness axiom it has a supremum
  obtain ⟨C, hC⟩ := hXsup -- get the supremum
  clear hXb hXn -- clean up some unnecessary hypothesis
  have hBup : (bound_above_by X C) := hC.left
  have hnup : ¬(bound_above_by X (C - b)) := by
    by_contra h -- assume it is an upper bound
    dsimp [supremum] at hC  -- break up the supremum
    rw [←bound_above_by] at hC  -- the supremum says that X is bounded above by C
    obtain ⟨h1, h2⟩ := hC
    specialize h2 (C - b) -- the new supremum is C - b
    rw [←bound_above_by] at h2  -- this means X is bounded above by C - b implies C ≤ C - b
    apply h2 at h
    linarith  -- obviously this is false

  have : ∃ (n : ℕ), n * b > C - b := by
    dsimp [bound_above_by] at hnup
    simp at hnup -- sort out the not 
    obtain ⟨x, hx1, hx2⟩ := hnup  -- get the hypothesis for being bounded above
    dsimp [X] at hx1
    obtain ⟨n, hn⟩ := hx1 -- get our needed n
    rw [←hn] at hx2 -- rewrite the definition of x
    use n -- with this n we have the goal
    

  obtain ⟨n, hn⟩ := this  -- get our n
  have hnxtinX : (n + 1) * b ∈ X := by  -- show that (n + 1) * b is in X
    use (n + 1)
    simp
  
  specialize hBup ((n + 1) * b) -- this (n + 1) * b is our needed element for the contradiction
  apply hBup at hnxtinX -- apply the contradition
  linarith  -- hence contradiction

def func_bound_above (X : Set ℝ) (f : ℝ → ℝ) : Prop := (∃ (c : ℝ), ∀ x ∈ X, f x ≤ c)

example : func_bound_above {x : ℝ | x ≤ 2} (fun x => x - 1) := by
  use 1 -- 1 is obviously the upper
  intro x hx  -- introduce variables
  norm_num  -- simplify the expression
  tauto -- naturally true

def func_sup (X : Set ℝ) (f : ℝ → ℝ) (C : ℝ) : Prop := func_bound_above X f ∧ (∀ B, (∀ x ∈ X, f x ≤ B) → C ≤ B)

example (X : Set ℝ) {hX : X = {x | x : ℝ}}: func_sup X (fun x => x / (1 + x ^ 2)) (1 / 2) := by
  dsimp [func_sup]  -- function supremum
  let f : ℝ → ℝ := fun x => x / (1 + x ^ 2) -- setting up an alias
  have hf : f = fun x => x / (1 + x ^ 2) := by trivial  -- setting up the subsitituion
  rw [←hf]  -- rewriting the definition of f
  clear hf  -- removing the bad hypothesis

  have h1 : ∀ x ∈ X, f x ≤ (1 / 2) := by  -- showing the upper bound
    -- doing a lot of stuff to show the upper bound
    dsimp [f]
    intro x hx
    cancel_denoms
    field_simp
    rw [div_le_comm₀ (by positivity) (by positivity)]
    simp
    rw [←zero_add (2 * x)]
    rw [←le_add_neg_iff_le]
    ring_nf
    calc
      0 ≤ (x - 1) ^ 2 := by positivity
      _ = x ^ 2 - 2 * x + 1 := by ring_nf
      _ = 1 - x * 2 + x ^ 2 := by ring_nf

  constructor -- breaking up the supremum
  . use 1 / 2 -- showing 1 / 2 is the bound
  . 
    specialize h1 1 -- having the upper bound at x = 1
    have : 1 ∈ X := by subst X; simp  -- showing 1 ∈ X
    
    intro B hB  -- introducing the upper bound
    specialize hB 1 -- setting the upper bound as 1
    apply hB at this  -- applying the expression for the bound
    norm_num at this  -- shoing the bound
    exact this  -- closing up the goal

def seq_is_limit (x : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - l| < ε

example : seq_is_limit (fun n => 6) 6 := by
  intro ε hε
  use 6
  simp [hε]

example (a : ℕ → ℝ) (ha : a = ((fun n => 1 / n) : ℕ → ℝ)) : seq_is_limit a 0 := by
  intro ε hε
  have h1 : ∃ (N : ℕ), N * ε > 1 := by exact archimedes _ _ hε  -- use archimedes to show there is a natural

  have h2 : ∃ (N : ℕ), N > 1 / ε := by  -- show that this natural is manipulable
    obtain ⟨N, hN⟩ := h1
    use N
    simp
    simp at hN
    rw [←Nat.div_one N, Nat.cast_div (by simp), Nat.cast_one, ←one_div] -- a bunch of rewriting to get the desired form
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
    norm_num
  
  obtain ⟨N, hN⟩ := h2
  use N
  intro n hn
  subst a
  
  simp [←one_div]
  have : 0 < n := by
    have h0 : (0 : ℝ) < N := by
      calc
        0 < 1 / ε := by positivity
        _ < N := by linarith
    suffices h : (0 < N) from by linarith
    field_simp at h0
    linarith
  
  rw [abs_of_nonneg (by simp)]
  rw [one_div_lt (by positivity) (by positivity)]
  calc
    1 / ε < N := hN
    _ ≤ n := by simp_all

theorem seq_uniquelim (h1 : seq_is_limit x l) (h2 : seq_is_limit x m) : l = m := by
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

theorem conv_seq_is_bounded (xn : ℕ → ℝ) (hx : seq_is_limit xn x) : seq_bound_above xn := by
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

theorem seq_squeeze_zero (x : ℕ → ℝ) (y : ℕ → ℝ) (hy : seq_is_limit y 0) : ∀ (n : ℕ), |x n| ≤ y n → seq_is_limit x 0 := by
  sorry

example : seq_is_limit (fun (n : ℕ) => (-1) ^ n / (√(n ^ 2 + n))) 0 := by
  have h : ∀ (n : ℕ), |(fun (n : ℕ) => (-1) ^ n / (√(n ^ 2 + n))) n| ≤ (fun (n : ℕ) => 1 / √(n)) n := by
    intro n
    simp [←one_div]
    calc
      |(-1) ^ n / (√(n ^ 2 + n))| = 1 / (√(n ^ 2 + n)) := by admit
      _ ≤ 1 / √(n + n) := by admit
      _ ≤ 1 / √(n) := by admit
  have h1 : seq_is_limit (fun (n : ℕ) => 1 / √(n)) 0 := by sorry
  apply seq_squeeze_zero _ _ h1
  tauto
