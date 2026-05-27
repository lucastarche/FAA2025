/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
set_option autoImplicit false
set_option tactic.hygienic false

-- DO NOT CHANGE THE THEOREM STATEMENT
-- Fill in the sorry

-- Most tactics are welcome.
-- You are now allowed to use `aesop` and `grind` tactics.

-- Problem 1
def SumOdd : ℕ → ℕ
  | 0 => 0
  | n + 1 => SumOdd n + (2*n +1)

theorem P1 (n : ℕ) : SumOdd (n) = n^2 := by
  induction' n with n ih
  · unfold SumOdd
    rfl
  · unfold SumOdd
    rw [ih]
    linarith

-- Problem 2 and 3
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
notation:10000 n "!" => factorial n

def isEven (n : ℕ) : Prop := ∃ k, n = 2*k

theorem P2 (n : ℕ) : isEven (n)! ↔ n ≥ 2 := by
  constructor
  · by_contra!
    obtain ⟨n_even, n_lt_2⟩ := this
    obtain ⟨k, hk⟩ := n_even
    if h: n = 0 then
      rw [h] at hk
      simp [factorial] at hk
      grind
    else
      have h: n = 1 := by grind
      rw [h] at hk
      simp [factorial] at hk
      grind
  · intro h
    induction' n, h using Nat.le_induction with n hn h
    · use 1
      rfl
    · obtain ⟨k, hk⟩ := h
      use (n + 1) * k
      rw [factorial, hk]
      linarith

theorem P3 : ∀ n > 0 , 3 ^ n > n ^ 2 := by
  have h2: ∀ n > 0, 3^n * 2 >= 2 * n + 1 := by
    intro n hn
    induction' n, hn using Nat.le_induction with n hn h
    · simp
    · grind

  intro n hn
  induction' n, hn using Nat.le_induction with n hn h
  · simp
  · grw [Nat.pow_add_one]
    calc
      (n + 1)^2 = n^2 + 2 * n + 1 := by ring
      _ < 3^n + 2 * n + 1 := by gcongr
      _ < 3^n + 3^n * 2 := by grind
      _ = 3^(n + 1) := by ring


-- # Problem 4:
-- in this problem, you are asked to solve the following recurrence relation.
-- g(n) = g(n/2) + 1, g(0) = 0
-- Prove that that g(n) ≤  Nat.log 2 n + 1 for all n
-- state the formal theorem and prove it

-- The following lemmas can be helpful
#check Nat.sub_add_cancel
#check Nat.le_log_of_pow_le

-- Hice el choclo más grande de la historia e ignoré las sugerencias pero no importa :)

def g : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + g ((n + 1) / 2)

#eval [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8]

lemma g_increasing' (n : ℕ) : g n <= g (n + 1) := by
  induction' n using Nat.strong_induction_on with n h
  · cases n
    · simp [g]
    simp [g]
    rw [Nat.add_assoc]
    simp
    if h2: (1 <= n_1 % 2) then
      simp [Nat.add_div, h2]
    else
      simp [Nat.add_div, h2]
      apply h
      omega

lemma g_increasing (n : ℕ) (m : ℕ) (h : n <= m) : g n <= g m := by
  induction' m, h  using Nat.le_induction with m h1 h2
  · rfl
  trans (g m)
  exact h2
  exact g_increasing' m

lemma g_pow_2 (n : ℕ) : g (2^n) = n + 1 := by
  induction' n with n h
  · unfold g
    simp [g]
  · have h2 : ∃ k, 2^(n + 1) = k + 1 := by aesop
    obtain ⟨k, hk⟩ := h2
    rw [hk, g, ← hk, pow_succ, Nat.add_comm]
    simp [h]

lemma g_prev_pow_2 (n : ℕ) : g (2^n - 1) = n := by
  induction' n with n ih
  · simp [g]
  cases h : 2^(n + 1) - 1
  · simp [Nat.pow_succ] at h
    have h2 : 0 < 2^n := by aesop
    have h3 : 1 <= 2^n := by grind
    omega
  rw [g, ← h]
  have h3 : (2^(n + 1) - 1) / 2 = 2^n - 1 := by grind
  rw [h3, ih, Nat.add_comm]

lemma g_lt_pow_2 (n : ℕ) (k : ℕ) (h : n < 2^k) : g n < g (2^k) := by
  rw [g_pow_2]
  have h2 : g n <= g (2^k - 1) := by
    apply g_increasing
    omega
  grw [h2, g_prev_pow_2]
  linarith

lemma g_eq_pow_log_2 (n : ℕ) : g (n + 1) = g (2^(Nat.log 2 (n + 1))) := by
  have lhs : Nat.log 2 (n + 1) + 1 <= g (n + 1) := by
    rw [← g_pow_2]
    apply g_increasing
    apply Nat.pow_log_le_self
    omega
  have rhs : g (n + 1) < Nat.log 2 (n + 1) + 2 := by
    nth_rw 2 [← g_pow_2]
    apply g_lt_pow_2
    apply Nat.lt_pow_succ_log_self
    trivial
  rw [g_pow_2]
  omega

theorem P4 (n : ℕ) : g n <= Nat.log 2 n + 1 := by
  cases n
  · simp [g]
  rw [g_eq_pow_log_2, g_pow_2]

-- # Problem 5
-- in this problem, you are asked to solve the following recurrence relation.
-- f(n) = 2*f(n-1) - f(n-2) + 2
-- where f(0) = 1 and f(1) = 1
-- Prove that that f(n) = n^2 - n + 1

-- state the formal theorem and prove it
-- Hint: you may find `zify` tactic useful

def f : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * f (n + 1) - f n + 2

lemma sq_gt_self (n : ℕ) : n <= n^2 := by
  induction' n with n ih
  · rfl
  ring_nf
  omega

theorem P5 (n : ℕ) : f n = n^2 - n + 1 := by
  induction' n using Nat.twoStepInduction with n h1 h2
  all_goals simp [f]
  rw [h1, h2]

  have h3 : 2 * ((n + 1)^2 - (n + 1) + 1) >= n^2 - n + 1 := by
    trans ((n + 1)^2 - (n + 1) + 1)
    · simp
    have n_pos : n >= 0 := by omega
    zify [n_pos, sq_gt_self n, sq_gt_self (n + 1)]
    ring_nf
    omega

  zify [h3, sq_gt_self n, sq_gt_self (n + 1), sq_gt_self (n + 2)]
  ring
