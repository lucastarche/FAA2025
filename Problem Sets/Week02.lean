/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option tactic.hygienic false

/- # Instruction
In this homework, you are not allowed to use tactics outside the basic tactics listed below.
Basic tactics: `rfl`, `intro`, `exact`, `constructor`, `apply`, `rw`, `left`, `right`, `cases`, `by_cases`, `ext`, `trivial`,`contradiction`,`assumption`,`have`, `by_contra`, `rintro`

If you need to use different tactics, please justify why basic tactics in the list above are not sufficient.
In particular, you are not allowed to use automation (simp, aesop, grind, ring, omega, etc) to finish the goal.

**Instruction**:
(1) Fill each `sorry` with the appropriate tactics.
(2) For each problem, give an informal explanation of the proof strategy. This should correspond to your Lean proof.
**Submission**:  HW1.lean file in Moodle. The grading will be based on (1) and (2).

-/
section
open Set
variable {α : Type*}
variable (A B C : Set α)

/-
TODO: Arreglar estos, medio que quedaron feuchos P2/P3
-/

/-
  Proof strategy for P1 is:
-/

lemma P1 : (B ∪ C) ⊆ A ↔ B ⊆ A ∧ C ⊆ A := by
  constructor
  · intro h
    constructor
    · intro x hx
      apply h
      left
      exact hx
    · intro x hx
      apply h
      right
      exact hx
  · intro ⟨h1, h2⟩ x hx
    cases hx
    · apply h1
      exact h
    · apply h2
      exact h

/-
  Proof strategy for P2 is:
-/

theorem P2 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext
  constructor
  · intro ⟨h1, h2⟩
    cases h2
    · left
      exact ⟨h1, h⟩
    · right
      exact ⟨h1, h⟩
  · intro h1
    cases h1
    · obtain ⟨h1, h2⟩ := h
      constructor
      · exact h1
      · left
        exact h2
    · obtain ⟨h1, h2⟩ := h
      constructor
      · exact h1
      · right
        exact h2

/-
  Proof strategy for P3 is:
-/

theorem P3 : (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C) := by
  ext x
  constructor
  · intro ⟨⟨h1, h2⟩, h3⟩
    cases h1
    · cases h3
      left
      left
      exact ⟨h, h_1⟩
      left
      right
      exact ⟨h, h_1⟩
    · cases h2
      left
      left
      exact ⟨h_1, h⟩
      right
      exact ⟨h, h_1⟩
  · intro h
    cases h
    · cases h_1
      · obtain ⟨ha, hb⟩ := h
        constructor
        · constructor
          · left
            exact ha
          · left
            exact ha
        · left
          exact hb
      · obtain ⟨ha, hc⟩ := h
        constructor
        · constructor
          all_goals
          left
          exact ha
        · right
          exact hc
    · obtain ⟨hb, hc⟩ := h_1
      constructor
      · constructor
        · right
          exact hb
        · right
          exact hc
      · right
        exact hc

-- The set difference operation is denoted by B \ A
-- This can be simplified using rw [mem_diff] where
#check mem_diff

-- In this theorem, the partial proof has been outlined.
-- Your task is to fill in the sorry
-- the following theorem can be helpful
#check subset_union_left

/-
  Proof strategy for P4 is:
-/

theorem P4 : (∃ X : Set α, A ∪ X = B) ↔ A ⊆ B := by
  constructor
  · -- Forward direction: if there exists X such that A ∪ X = B, then A ⊆ B
    intro h
    obtain ⟨x, hx⟩ := h
    rw [← hx]
    apply subset_union_left
  · -- Reverse direction: if A ⊆ B, then there exists X such that A ∪ X = B
    intro h           -- "Assume A ⊆ B"
    use B \ A         -- "Let X = B \ A"
    ext x
    constructor
    · intro h2
      cases h2
      apply (h h_1)
      rw [mem_diff] at h_1
      exact h_1.left
    · intro h2
      by_cases h3: (x ∈ A)
      · left
        exact h3
      · right
        rw [mem_diff]
        exact ⟨h2, h3⟩
end

section
variable {α : Type*} [DecidableEq α]
variable (A B C : Finset α)

open Finset
-- Finset is a set whose cardinality is bounded
-- If A is a Finset, then #A is the cardinality of the set

/- Recall rw tactics:
If thm is a theorem a = b, then as a rewrite rule,
  rw [thm] means to replace a with b, and
  rw [← thm] means to replace b with a.
-/

def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k
def IsDisjoint (A B: Finset α) : Prop := A ∩ B = ∅

-- you may find the following operations useful
#check card_union
#check card_eq_zero
#check Nat.two_mul


/-
  Proof strategy for P5 is:
-/

theorem P5 (U : Finset α) (A B : Finset α)
(hAB : IsDisjoint A B) (hcard : #A = #B) (htotal : A ∪ B = U) : IsEven (#U) := by
  -- Hint: First prove the following claim:
  have AB_eq: #(A ∪ B) = #A + #B := by
    rw [card_union, hAB]
    nth_rw 3 [card_eq_zero.mpr]
    repeat rfl

  -- Then use AB_eq to finish the proof
  use #A
  rw [Nat.two_mul]
  nth_rw 2 [hcard]
  rw [← AB_eq, htotal]
