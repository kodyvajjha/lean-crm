import .random_variable
import measure_theory.measure_space
import measure_theory.integration

open lattice measure_theory ennreal

universe u 

local attribute [instance] classical.prop_decidable
noncomputable theory 

variables {s α : Type u} [probability_space s] (p : probability_measure s) {X : s → ℝ} [hX : measurable X]

/-- Value-at-Risk at level a-/
def VaR {a : nnreal} (hX : measurable X) (ha : a ∈ set.Ioo (0:nnreal) (1:nnreal)) : ℝ := Inf { x : ℝ | distribution_function p hX x ≥ a }  

def Icc_ind (p : ennreal) : ennreal → ennreal :=
λ h : ennreal, if  h ∈  (set.Icc p (1:ennreal)) then (1* (1/1-p):ennreal) else (0:ennreal)

/-- Expected Shortfall at level a-/
def ES {a : nnreal} (X : s → ℝ) (hX : measurable X) (ha : a ∈ set.Ioo (0:nnreal) (1:nnreal))
: ennreal  := 
measure.integral (@measure_theory.measure_space.μ ℝ _) (λ h, ennreal.of_real(VaR p hX ha) * Icc_ind a (ennreal.of_real h) )

