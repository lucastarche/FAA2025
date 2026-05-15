import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card

/- This exercise covers the essential concepts from Week 2:
- Quantifiers: universal (∀) and existential (∃)
- Set theory basics: membership (∈), subset (⊆), union (∪), intersection (∩)
- New tactics: `intro`, `use`, `obtain`, `left`, `right`, `cases`, `by_cases`, `ext`, `rintro`
- Set operations and extensionality principles
-/

/-! ## Part 1: Quantifiers and Basic Logic

Working with universal (∀) and existential (∃) quantifiers.
Remember: `∀ x, P x` is the same as `(x : α) → P x` in Lean.
-/

section Quantifiers

-- Exercise 1: Basic universal quantifier
-- Hint: Use `intro` to assume an arbitrary element, then prove the property
example : ∀ n : ℕ, n + 0 = n := by
  intro n
  rfl

-- Exercise 2: Basic existential quantifier
-- Hint: Use `use` to provide a witness that satisfies the property
example : ∃ n : ℕ, n + 3 = 7 := by
  use 4

-- Exercise 3: Multiple existentials
-- Hint: Provide witnesses for both variables using `use`
example : ∃ n m : ℕ, n + m = 5 := by
  use 2, 3

-- Definition for even numbers
def IsEven (n : ℤ) : Prop := ∃ k, n = 2 * k

-- Exercise 4: Working with definitions
-- Hint: Use `obtain` to extract the witness and property from the existential
example (h : ∃ n : ℤ, IsEven n ∧ n > 10) : ∃ m : ℤ, m > 5 := by
  obtain ⟨n, ⟨h1, h2⟩⟩ := h
  use n
  trans 10
  · exact h2
  · trivial

-- Exercise 5: Combining quantifiers with logic
-- Hint: Unfold the definition, obtain the witness, then provide a new witness
example (n : ℤ) (h : IsEven n) : IsEven (n + 2) := by
  obtain ⟨k, hk⟩ := h
  use k + 1
  rw [hk]
  rw [mul_add]
  trivial

end Quantifiers

/-! ## Part 2: Set Theory Fundamentals

Basic set operations and their properties.
Sets in Lean are functions α → Prop.
-/

section SetBasics

open Set
variable {α : Type*}
variable (A B C D : Set α)

-- Exercise 6: Reflexivity of subset
-- Hint: Rewrite using subset definition, then use `intro` and `assumption`
#check subset_def
example : A ⊆ A := by
  intro x hx
  assumption

-- Exercise 7: Empty set is subset of everything
-- Hint: Use subset definition, then `exfalso` to derive contradiction from empty set membership
example : ∅ ⊆ A := by
  intro x hx
  exfalso
  exact hx

-- Exercise 8: Transitivity of subset
-- Hint: Use subset definition, then chain the implications
example : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro h_ab h_bc x hx
  apply h_bc
  apply h_ab
  exact hx

-- Exercise 9: Intersection subset
-- Hint: Use subset and intersection definitions
example : A ∩ B ⊆ B := by
  intro x ⟨h1, h2⟩
  assumption

-- Exercise 10: Subset intersection characterization
-- Hint: Use constructor to split the conjunction, then prove each direction
example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
  intro h_ab h_ac x hx
  constructor
  · exact h_ab hx
  · exact h_ac hx

end SetBasics

/-! ## Part 3: Disjunctions and Case Analysis

Working with logical OR (∨) and case analysis.
-/

section Disjunctions

open Set
variable {α : Type*}
variable (A B C : Set α)

-- Exercise 11: Left inclusion in union
-- Hint: Use `left` to choose the first disjunct
example : A ⊆ A ∪ B := by
  intro x hx
  left
  assumption

-- Exercise 12: Case analysis with excluded middle
-- Hint: `by_cases` splits into two cases automatically
example (x : α) : x ∈ A ∨ x ∉ A := by
  by_cases h : x ∈ A
  · left
    assumption
  · right
    assumption

-- Exercise 13: Union subset characterization
-- Hint: Use constructor for the biconditional, then `cases` to handle the union
#check mem_union
lemma union_subset_iff : A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  constructor
  · intro ⟨h_ac, h_bc⟩ x hx
    cases hx
    · rename_i h
      exact h_ac h
    · rename_i h
      exact h_bc h
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

-- Exercise 14: Using the characterization
-- Hint: Apply the lemma you just proved
example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
  intro h_ba h_ca
  apply (union_subset_iff B C A).mp
  exact ⟨h_ba, h_ca⟩

end Disjunctions
