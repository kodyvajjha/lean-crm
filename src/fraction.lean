-- import algebra.field
import data.rat data.nat.modeq order.lattice 
import tactic.tidy 
import data.padics.padic_norm
import data.padics.padic_integers
import data.nat.prime 
import data.zmod.basic
import set_theory.cardinal
import tactic.find
open rat nat lattice list padic_val_rat multiplicity 

section harmonic

variable [prime_two : nat.prime 2]
include prime_two


local infix ` /. `:70 := mk

variable x:ℚ

def harmonic_number : ℕ → ℚ
| 0 := 0
| 1 := 1
| (succ n) := (harmonic_number n) + 1 /. (n+1)

@[simp] lemma finite_two (q : ℕ) (hq : q ≠ 0) : finite 2 q := 
begin 
  apply (@finite_nat_iff 2 q).2,
  split, exact (prime.ne_one prime_two),
  apply nat.pos_of_ne_zero, assumption
end

lemma two_val_neg_denom_even (x : ℚ) : (x ≠ 0) → (padic_val_rat 2 x < 0) → 2 ∣ x.denom :=
begin
  intros h₁ h₂,
  rw padic_val_rat_def _ h₁ at h₂, swap, exact prime_two,
  rw [sub_lt_zero] at h₂,
  have := lt_of_le_of_lt (int.coe_nat_nonneg _) h₂,
  have := int.coe_nat_pos.1 this,
  rw [←enat.coe_lt_coe,enat.coe_get] at this, 
  replace := dvd_of_multiplicity_pos this, 
  rw int.coe_nat_dvd at this, assumption,
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

def max_pow_2_below (n : ℕ) := nat.find_greatest (λ (m : ℕ), 2^m ≤ n) n  

lemma max_pow_le (n : ℕ) : 
(n ≥ 1) → 2^(max_pow_2_below n) ≤ n := 
begin
  intro h,
  apply @find_greatest_spec (λ (m : ℕ), 2^m ≤ n), simp, 
  existsi 0, simpa,
end

lemma is_lt_max_pow_plus_one (n : ℕ) : (n ≥ 1) →  n < 2^((max_pow_2_below n) + 1) :=
begin
  intro h,
  by_contra,
  rw not_lt at a,
  have k : (max_pow_2_below n + 1) ≤ max_pow_2_below n, {
    apply le_find_greatest,
    swap, exact a,
    -- induction n with m n h, simp at *, 
    sorry 
  },
  have := nat.le_sub_left_of_add_le k, simp at this, assumption 
end


lemma two_val_add_eq_min {q r : ℚ} (hne : padic_val_rat 2 q ≠ padic_val_rat 2 r) :
  padic_val_rat 2 (q + r) = min (padic_val_rat 2 q) (padic_val_rat 2 r) :=
sorry 

lemma two_val_le_max_pow (x n : ℕ) (hx : x ≤ n)(hn : n ≥ 1) :(padic_val_rat 2 x) ≤ (max_pow_2_below n) :=
begin
  by_contra,
  rw not_le at a, 
  sorry,
end

lemma two_val_sum_pow_two (n k : ℕ)(h₀ : k ≠ 0)(hn : n ≥ 1)(hk : k < n) : padic_val_rat 2 k ≠ (max_pow_2_below n) → padic_val_rat 2 (1 /. k + 1 /. 2^(max_pow_2_below n)) = -max_pow_2_below n  := 
begin
  intros,
  rw two_val_add_eq_min,
  all_goals {rw [two_val_rec_pow_two,←inv_def,←coe_int_eq_mk],simp,rw padic_val_rat.inv}, swap, simpa,
  rw min_neg_neg, simp,
  apply max_eq_right, 
  apply two_val_le_max_pow, apply le_of_lt hk, tidy,
end


theorem valuation_harmonic_number (n : ℕ) (hn : n ≥ 1) : padic_val_rat 2 (harmonic_number n) + max_pow_2_below n = 0 := 
sorry


-- lemma odd_denoms (q₁ q₂ : ℚ) (h₁ : ↑(denom q₁) % 2 = 1) (h₂ : ↑(denom q₂) % 2 = 1) : ((denom (q₁ + q₂)) % 2 = 1) :=
-- begin
--   rw add_num_denom, 
--   have h : ((q₁.num * ↑(q₂.denom) + ↑(q₁.denom) * q₂.num) /. (↑(q₁.denom) * ↑(q₂.denom))).denom = (↑(q₁.denom) * ↑(q₂.denom)), by sorry,
--   rw h,
--   apply odd_mul_odd h₁ h₂,
-- end

end harmonic