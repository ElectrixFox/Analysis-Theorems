import Mathlib

def seq_is_limit (x : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - l| < ε

open BigOperators

open Finset

def seq_partial_sums (a : ℕ → ℝ) : ℕ → ℝ := fun n => (∑ i ∈ Icc 0 n, a i)

lemma sum_start' (a : ℕ → ℝ) (N : ℕ := 0) {n : ℕ}  : ∑ i ∈ Icc N n, a i = ∑ i ∈ Icc 0 n, a i - ∑ i ∈ Icc 0 (N - 1), a i := by
  rw [←sum_Ico_add_eq_sum_Icc]

lemma sum_add (a : ℕ → ℝ) {n : ℕ} : ∑ i ∈ Icc 0 (n + 1), a i = (∑ i ∈ Icc 0 n, a i) + a (n + 1) := by
  simp [sum_Icc_succ_top]

lemma sum_add' (a : ℕ → ℝ) (N : ℕ := 0) {n : ℕ} : ∑ i ∈ Icc N (n + 1), a i = (∑ i ∈ Icc N n, a i) + a (n + 1) := by
  rw [sum_Icc_]

example : ∀ (n : ℕ), (seq_partial_sums (fun n => n)) n = (fun (n : ℕ) => (n * (n + 1) : ℝ) / 2) n := by
  intro n
  induction' n with k hk
  .
    simp [seq_partial_sums]
  . 
    simp [seq_partial_sums]
    rw [sum_add]
    dsimp [seq_partial_sums] at hk
    rw [hk]
    field_simp
    ring_nf

def sum_is_limit (x : ℕ → ℝ) (l : ℝ) : Prop := seq_is_limit (seq_partial_sums x) l

def seq_partial_sums' (a : ℕ → ℝ) (N : ℕ := 1) : ℕ → ℝ := fun n => (∑ i ∈ Icc N n, a i)

example : ∀ (n : ℕ), ∀ N ≤ n, (seq_partial_sums' (fun n => n) N) n = (fun (n : ℕ) => (n * (n + 1) : ℝ) / 2) n - (fun (n : ℕ) => (n * (n + 1) : ℝ) / 2) N := by
  intro n N hn
  induction' n with k hk
  . simp_all [seq_partial_sums']
  . 
    simp [seq_partial_sums']
    rw [sum_add]
