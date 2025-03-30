import AnalysisTheorems.Sets

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

example : func_bound_above {x : ℝ | x ≤ 2} (fun x => x - 1) := by
  use 1 -- 1 is obviously the upper
  intro x hx  -- introduce variables
  norm_num  -- simplify the expression
  tauto -- naturally true

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
