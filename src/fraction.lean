-- import algebra.field
import data.rat data.nat.modeq order.lattice 
import tactic.tidy 
import data.padics.padic_norm
import data.padics.padic_integers
import data.nat.prime 
import set_theory.cardinal
open rat nat lattice list padic_val_rat

section harmonic

variable [prime_two : nat.prime 2]
include prime_two


local infix ` /. `:70 := mk

def harmonic_number : ℕ → ℚ
| 0 := 0
| 1 := 1
| (succ n) := (harmonic_number n) + 1 /. (n+1)


lemma odd_denoms (q₁ q₂ : ℚ) (h₁ : ↑(denom q₁) % 2 = 1) (h₂ : ↑(denom q₂) % 2 = 1) : ((denom (q₁ + q₂)) % 2 = 1) :=
begin
  rw add_num_denom, 
  have h : ((q₁.num * ↑(q₂.denom) + ↑(q₁.denom) * q₂.num) /. (↑(q₁.denom) * ↑(q₂.denom))).denom = (↑(q₁.denom) * ↑(q₂.denom)), by sorry,
  rw h,
  apply odd_mul_odd h₁ h₂,
end

def max_pow_2_below (n : ℕ) := nat.find_greatest (λ (m : ℕ), 2^m ≤ n) n  


lemma max_pow_le (n : ℕ) : 
(n ≥ 1) → 2^(max_pow_2_below n) ≤ n := 
begin
  intro h,
  apply @find_greatest_spec (λ (m : ℕ), 2^m ≤ n), simp, 
  existsi 0, simpa,
end

lemma two_val_rec_pow_two (r : ℕ) : padic_val_rat 2 (1 /. (2^r)) = -r := 
begin
  rw [←inv_def,←coe_int_eq_mk], simp,
  rw padic_val_rat.inv,
  {
    rw padic_val_rat.pow, 
    have h : padic_val_rat 2 2 = padic_val_rat 2 ↑2, by refl,
    rw h,
    rw padic_val_rat_self one_lt_two,
    simp, exact two_ne_zero,
  },
  apply pow_ne_zero, exact two_ne_zero, 
end

#check multiplicity
#check padic_val_rat
lemma two_val_le_max_pow (n k : ℕ) (hk : k < n) : padic_val_rat 2 k ≤ max_pow_2_below n := 
begin
  by_cases (k = 0),
  simp [h],
  rw padic_val_rat_def, simp, 
  
end

lemma two_val_add_eq_min {q r : ℚ} (hne : padic_val_rat 2 q ≠ padic_val_rat 2 r) :
  padic_val_rat 2 (q + r) = min (padic_val_rat 2 q) (padic_val_rat 2 r) :=
sorry 

#check min_neg_neg 

lemma two_val_sum_pow_two (n k : ℕ) (h₀ : k ≠ 0)(hk : k < n) (r := max_pow_2_below n) : padic_val_rat 2 (1 /. k + 1 /. 2^r) = -r := 
begin
  rw two_val_add_eq_min,
  all_goals {rw [two_val_rec_pow_two,←inv_def,←coe_int_eq_mk],simp,rw padic_val_rat.inv},
  rw min_neg_neg, 
  --  rw [←inv_def,←coe_int_eq_mk], simp, 
  --  rw padic_val_rat.inv,
  
end

-- theorem valuation_harmonic_number (n : ℕ) : padic_val_rat 2 (harmonic_number n) + max_pow_2_below n = 0 := sorry

-- #eval padic_val_rat 2 (1/.8) 
-- #eval max_pow_2_below 8

-- example : padic_val_rat 2 (harmonic_number 5) + max_pow_2_below 5 = 0 := by sorry




-- lemma principle_of_domination (n : ℕ) (x : ℚ):
-- padic_val_rat p ((finset.range n).sum (λ x, (x:ℚ))) = padic_val_rat p x := sorry

end harmonic