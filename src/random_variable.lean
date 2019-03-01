/-
Copyright (c) 2018 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

A formalization of properties of random variables.
-/

import .probability_theory tactic.tidy
import order.filter
import measure_theory.lebesgue_measure measure_theory.borel_space
import topology.basic
open set measurable_space measure_theory ennreal lattice filter
set_option pp.implicit true

universe u

variables {s α : Type u} [probability_space s] (p : probability_measure s) (a : set s)

local attribute [instance] classical.prop_decidable

section random_variable

def is_random_variable (X : s → ℝ) := measurable X

-- lemma is_random_variable_leq (X : s → ℝ) :
-- is_random_variable(X) ↔ ∀ x:ℝ, is_measurable({ω : s | X ω ≤ x}) :=
-- begin
-- fsplit,
-- {
--   intros h x,
--   have g : {ω : s | X ω ≤ x} = X⁻¹'({z:ℝ| z ≤ x}), by refl,
--   rw g,
--   apply h,
--   refine measurable_le measurable_id measurable_const,
-- },
-- {
--   intros h,
--   unfold is_random_variable, unfold measurable,
--   -- rw borel_eq_generate_Iio,
--   unfold measurable_space.map,
--   intros b g, dsimp at *,
--   unfold set.preimage,

--   have h₀: ∀ ω :s , X ω ∈ b → X ω ≤ Sup b, {
--     -- intros ω h, apply le_Sup h,

--   }

-- }
-- end

-- #print instances complete_lattice

noncomputable def indicator (a : set s) :=(λ x : s, if x ∈ a then (1:ℝ) else 0)

lemma indicator_in (a  : set s) (x : s)
(h : x ∈ a) : indicator a x = 1  := by simp [indicator,h]


lemma indicator_nin (a  : set s) (x : s)
(h : x ∉ a) : indicator a x = 0 := by simp [indicator,h]


/- TODO: Shorten these proofs. -/
lemma indicator_map_1 (a : set s)
(b : set ℝ)
(h₁ : (0:ℝ) ∈ b)
(h₂ : (1:ℝ) ∈ b)
: (indicator a ⁻¹' b) = univ :=
begin
ext1, dsimp at *, by_cases (x ∈ a),
{
  split,
  intros h₁, rw indicator_in a x h at h₁, apply mem_univ,
  intros h₂, rw indicator_in a x h, assumption,
},
{
  split,
  intros g₁, rw indicator_nin a x h at g₁, apply mem_univ,
  intros g₂, rw indicator_nin a x h, assumption,
}
end


lemma indicator_map_2 (a : set s)
(b : set ℝ)
(h₁ : (0:ℝ) ∉ b)
(h₂ : (1:ℝ) ∈ b)
: (indicator a ⁻¹' b) = a :=
begin
  ext1, dsimp at *, fsplit, by_cases(x ∈ a),
  {
    intros k, assumption,
  },
  {
    intros k, rw indicator_nin a x h at k, exfalso, apply h₁ k,
  },
  {
    intros k, rw indicator_in a x k, assumption,
  },
end

lemma indicator_map_3 (a : set s)
(b : set ℝ)
(h₁ : (0:ℝ) ∈ b)
(h₂ : (1:ℝ) ∉ b)
: (indicator a ⁻¹' b) = -a :=
begin
  tidy,
  rw indicator_in a x a_2 at a_1,
  apply h₂ a_1,
  rw indicator_nin a x a_1, assumption,
end

lemma indicator_map_4 (a : set s)
(b : set ℝ)
(h₁ : (0:ℝ) ∉ b)
(h₂ : (1:ℝ) ∉ b)
: (indicator a ⁻¹' b) = ∅ :=
begin
  ext1, dsimp at *, by_cases (x ∈ a),
  {
    split,
    intros h₁, rw indicator_in a x h at h₁, apply h₂ h₁,
    intros h₂, exfalso, exact h₂,
  },
  {
    split,
    intros g₁, rw indicator_nin a x h at g₁, apply h₁ g₁,
    intros g₂, exfalso, exact g₂,
  }
end

lemma is_random_variable_indicator {a : set s} (g : is_measurable a) : is_random_variable(indicator a) :=
begin
intros b h,
unfold measurable_space.map, dsimp,
by_cases g₁: ((0:ℝ) ∈ b),
{
  by_cases g₂: ((1:ℝ) ∈ b),
  rw indicator_map_1 a b g₁ g₂, apply is_measurable.univ,
  rw indicator_map_3 a b g₁ g₂, apply is_measurable.compl g,
},
{
  by_cases g₂: ((1:ℝ) ∈ b),
  rw indicator_map_2 a b g₁ g₂, assumption,
  rw indicator_map_4 a b g₁ g₂, apply is_measurable.empty,
}
end

lemma is_random_variable_add (X Y : s → ℝ) (h₁ : is_random_variable X) (h₂ : is_random_variable Y) :
is_random_variable( X + Y ) :=
begin
apply measurable_add, repeat{assumption},
end

lemma is_random_variable_mul (X Y : s → ℝ) (h₁ : is_random_variable X) (h₂ : is_random_variable Y) :
is_random_variable( X * Y ) :=
begin
apply measure_theory.measurable_mul, repeat{assumption},
end

-- theorem is_random_variable_lim' (Z : ℕ → (s → α))
-- (h : Π i:ℕ, is_random_variable (Z i))
--  (Z' : s → ℝ)
--  (h : ∀ ω : s, tendsto (λ i:ℕ, Z i ω) at_top (nhds(Z' ω))):
-- (is_random_variable Z')
-- := sorry

-- theorem is_random_variable_lim (Z : ℕ → (s → ℝ))
-- (h : Π i:ℕ, is_random_variable (Z i))
--  (Z' : s → ℝ)
--  (h : ∀ ω : s, tendsto (λ i:ℕ, Z i ω) at_top (nhds(Z' ω))):
-- (is_random_variable Z')
-- :=
-- begin
--   intros b g,
--   unfold measurable_space.map, dsimp,
--   unfold set.preimage,
--   unfold tendsto at h,
--   sorry
-- end

end random_variable

section distribution_function

def distribution_function (X : s → ℝ) :=
(λ x:ℝ, prob p({ω : s | X(ω) ≤ x}))

end distribution_function
