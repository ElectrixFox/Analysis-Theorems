import Mathlib

set_option trace.Elab.info true

def seq_is_limit (x : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - l| < ε

example : seq_is_limit (fun n => 6) 6 := by
  intro ε hε
  use 6
  intro n hn

  rwa [show |_| < ε ↔ 0 < ε by ring_nf; rw [abs_zero]]
