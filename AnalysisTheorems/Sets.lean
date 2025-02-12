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

example (X : Set ℝ) (hX : X = {x | x : ℝ}) : func_sup X (fun x => x / (1 + x ^ 2)) (1 / 2) := by
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
  
