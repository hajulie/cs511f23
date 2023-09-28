import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- Problem 4a 
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  have hxt'' := 
    calc 
      0 < (-x) * t := by addarith [hxt] 
      _ = x * (-t) := by ring 
  cancel x at hxt'' 
  have ht : t < 0 := by addarith [hxt''] 
  apply ne_of_lt 
  apply ht 

-- Problem 4b 
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use (a+1 : ℤ)
  use (a : ℤ)
  calc 
    (a+1)^2 - a^2 = a^2 + 2*a + 1 - a^2 := by ring 
    _ = 2*a + 1 := by ring 

-- Problem 4c 
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  have h1 := 
    calc
      p = (p+p) / 2 := by ring
      _ < (p+q) / 2 := by rel [h] 
  apply h1 
  have h2 := 
    calc
      (p+q) / 2 < (q+q) / 2 := by rel [h]
      _ = q := by ring 
  apply h2 

-- Problem 5a 
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have H := le_or_gt x 0 
  obtain hx | hx := H 
  use x + 1 
  calc 
    (x+1)^2 = x^2 + 2*x + 1 := by ring 
    _ = x * x + 2 * x + 1 := by ring 
    _ 

-- Problem 5b
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨ a , hx ⟩ := h 
  have h1 : (1-a) * (t-1) := by 


  have H := le_or_gt a 1
  obtain hy | hy := H 
  have h1 : (1-a)*(t-1) > 0 := by addarith [hx]


-- Problem 5c
-- example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a , ha ⟩ := h 
  intros m'
  