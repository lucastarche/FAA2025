import Mathlib.Tactic



section BasicLogic

/-! ## Basic Logic

These exercises practice the fundamental logical reasoning tactics.
Remember:
- Use `intro` to introduce hypotheses for implications
- Use `exact` when you have exactly what you need
- Use `constructor` to split goals like `P ∧ Q` or `P ↔ Q`
-/

variable (P Q R : Prop)

-- Example: reflexivity of implication
example : P → P := by
  intro h
  exact h

-- Exercise 3: Simple implication chain
example : P → (Q → P) := by
  intro hp hq
  exact hp

-- Exercise 4: Transitivity of implication
example : (P → Q) → (Q → R) → (P → R) := by
  intro pq qr p
  exact (qr ∘ pq) p

-- Exercise 5: Conjunction introduction
example (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩

-- Exercise 6: Conjunction commutativity
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  repeat
    intro ⟨h1, h2⟩
    exact ⟨h2, h1⟩

-- Exercise 7: More complex logical reasoning
example : (P → Q) ∧ (P → R) → (P → Q ∧ R) := by
  intro ⟨pq, pr⟩ p
  exact ⟨pq p, pr p⟩

end BasicLogic


section ApplyTactic

variable (P Q R S : Prop)

-- Example: basic apply usage
example (h1 : P → Q) (h2 : P) : Q := by
  apply h1
  exact h2

-- Exercise 8: Chaining apply
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  apply h2
  apply h1
  apply h3

-- Exercise 9: Apply with multiple premises (from w1sheet2 style)
example (h0 : P ∧ Q ∧ R) (h : P → Q → R → S) : S := by
  obtain ⟨p, q, r⟩ := h0
  exact h p q r

-- Exercise 10: Mixed apply and intro
example : (P → Q) → (Q → R) → (P → R) := by
  intro h1 h2 p
  apply h2
  apply h1
  exact p

-- Hint: Chain the implications by working backwards from the goal
example (P Q R : Prop) : ((P → Q) ∧ (Q → R)) → (P → R) := by
  intro ⟨pq, qr⟩ p
  exact qr (pq p)


end ApplyTactic

section Functions

def f := fun x : ℕ ↦ fun y : ℕ ↦ x = y

-- Exercise 11: Basic function application
example : f 0 0 := by rfl

-- Exercise 12: Function reasoning
example (x : ℕ) : f 0 x → x = 0 := by
  intro h
  rw [f] at h
  rw [h]

-- Exercise 13: Function with inequality
example (x : ℕ) : f x 1 → x ≠ 2 := by
  intro h
  rw [f] at h
  rw [h]
  trivial

-- Exercise 14: More complex function reasoning
example (x y : ℕ) : f 0 x ∧ f 0 y → x = y := by
  intro ⟨h₁, h₂⟩
  rw [f] at h₁
  rw [f] at h₂
  rw [← h₁, ← h₂]

end Functions
