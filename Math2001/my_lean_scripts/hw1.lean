-- Julie Ha 

import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

-- Problem 3a 
theorem Problem3a{P Q R: Prop} (h : P ∧ Q → R) : P → (Q → R) := by 
intro h_P h_Q 
have h_PQ := by apply And.intro h_P h_Q
apply h h_PQ 

-- Problem 3b 
theorem Problem3b{p q r : Prop} (h : p → (q → r)) : (p → q) → (p → r) := by
intro h_pq h_p 
have h_q := by apply h_pq h_p 
have h_qr : q → r := by apply h h_p 
apply h_qr h_q 

-- Problem 3c 
axiom notnotE {p : Prop} (h : ¬ ¬ p) : p
theorem Problem3c {p q r: Prop} (h: (p ∧ ¬q → r)) (h_nr: ¬r) (h_p: p): q := by 
have h_nq : ¬¬q 
intro h_nq
have h_pnq := by apply And.intro h_p h_nq 
have h_r := by apply h h_pnq 
apply h_nr h_r 
apply notnotE h_nq 

-- Question 4 

-- 4a 
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
calc 
a = 2*b + 5 := by rw [h1]
_ = 2*3 + 5 := by rw [h2] 
_ = 6 + 5 := by ring 
_ = 11 := by ring 

-- 4b 
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
calc 
  x = (x+4) - 4 := by ring 
  _ = 2-4 := by rw [h1] 
  _ = -2 := by ring 

-- 4c 
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc 
  a = (a - 5*b) + 5*b := by ring 
  _ = 4 + 5*b := by rw [h1]
  _ = -6 + 5*(b+2) := by ring 
  _ = -6 + 5 * 3 := by rw [h2]
  _ = 9 := by ring 
