import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- HOMEWORK

-- Problem 4a 
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨ k, hk ⟩ := hn 
  use 7*k+1
  calc 
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring 

-- Problem 4b 
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at * 
  obtain ⟨ a , ha ⟩ := hx 
  obtain ⟨ b , hb ⟩ := hy 
  use 2*a*b + 3*b + a + 1 
  calc 
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2*a*b + 3*b + a + 1) + 1 := by ring 

-- Problem 4c (3.1.8)
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even, Odd] at *
  obtain ⟨ a, ha ⟩ := hn 
  use 2*a^2+2*a-3
  calc 
    n ^ 2 + 2 * n - 5 = (a+a)^2 + 2*(a+a) - 5 := by rw [ha] 
    _ = 2 * (2*a^2 + 2*a - 3) + 1 := by ring 

-- Problem 4d 

-- Problem 5a (4.1.3)
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h1 : (a+b)/2 ≥ a ∨ (a+b)/2 ≤ b := by apply h 
  obtain hx | hy := h1 
  calc 
    b = 2 * ((a+b)/2) - a := by ring 
    _ ≥ 2 * a - a := by rel [hx] 
    _ = a := by ring  
  calc 
    a = 2* ((a+b)/2 )- b := by ring 
    _ ≤ 2 * b - b := by rel [hy] 
    _ = b := by ring 

--  Problem 5b (4.1.6)
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3 
  intro x y h 
  have h1 := by 
    calc 
      (x+y)^2 ≤ (x+y)^2 + (x-y)^2 := by extra 
      _ = 2*(x^2+y^2) := by ring 
      _ ≤ 2 * 4 := by rel [h] 
      _ ≤ 3^2 := by numbers 
  have h2 := by 
    apply abs_le_of_sq_le_sq' h1 
    numbers
  obtain ⟨ hl, hr ⟩ := h2 
  apply hl 
   
-- Problem 5c (4.1.10 Exercise 2)

-- Problem 5d

-- Problem 6a ( 4.2.5 )
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor 
  · intro h
    have h1 := 
      calc 
        (x+3)*(x-2) = x^2 + x-6 := by ring 
        _ = 0 := by rw [h]
    have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
    obtain  hl | hr := h2 
    left 
    calc 
      x = (x+3)-3 := by ring 
      _ = (0) - 3 := by rw [hl]
      _ = -3 := by numbers  
    right 
    calc
      x = (x-2)+2 := by ring 
      _ = 0 + 2 := by rw [hr] 
      _ = 2 := by numbers
  · intro h 
    obtain hl | hr := h 
    calc 
      x ^ 2 + x - 6 = (-3)^2 + (-3) - 6 := by rw [hl] 
      _ = 9 - 3 - 6 := by ring 
      _ = 0 := by numbers 
    calc 
      x ^ 2 + x - 6 = (2)^2 + (2) - 6 := by rw [hr] 
      _ = 4 + 2 - 6 := by ring 
      _ = 0 := by numbers 
  
-- Problem 6a ( 4.2.6 )
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor 
  · intro h 
    have h1 := by 
      calc 
        (2*a-5)^2 = 4*(a^2-5*a+5) +5 := by ring 
        _ ≤ 4 * (-1) + 5 := by rel [h] 
        _ = 1^2 
    have h2 := 
    
    
  


  

   

