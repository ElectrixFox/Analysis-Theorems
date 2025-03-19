import Mathlib.Tactic

def divisible (a b : ℕ) : Prop := ∃ (c : ℕ), a = b * c

-- notation:50 a " ∣ " b => divisible a b

lemma one_divs (a : ℕ) : 1 ∣ a := by
  dsimp [(· ∣ ·)]
  use a
  norm_num

def is_prime (p : ℕ) : Prop := p > 1 ∧ ¬∃ c, c ≠ 1 ∧ c ≠ p → c ∣ p

theorem all_prod_of_prime : ∀ (a : ℕ), a > 1 → ∃ c, c ≠ 1 ∧ c ≠ a → c ∣ a := by
  intro a ha
  by_cases h : is_prime a
  . 
    dsimp [is_prime] at h
    obtain ⟨_, h1⟩ := h
    push_neg at h1
    specialize h1 a
    simp_all
  . 
    dsimp [is_prime] at h
    push_neg at h
    apply h at ha
    obtain ⟨c, hc⟩ := ha
    use c
