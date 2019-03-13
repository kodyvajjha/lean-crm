import .random_variable
import measure_theory.measure_space
import measure_theory.integration

open lattice measure_theory ennreal set

universe u 

local attribute [instance] classical.prop_decidable
noncomputable theory 

variables {s α : Type u} [probability_space s] (p : probability_measure s) {X : s → ℝ} (hX : measurable X)

/-- Value-at-Risk at level a-/
def VaR {a : nnreal} (hX : measurable X) (ha : a ∈ Ioo (0:nnreal) (1:nnreal)) : ℝ := Inf { x : ℝ | distribution_function p hX x ≥ a }  

def Icc_ind (p : ennreal) : ennreal → ennreal :=
λ h : ennreal, if  h ∈  (set.Icc p (1:ennreal)) then (1* (1/1-p):ennreal) else (0:ennreal)

/-- Expected Shortfall at level a-/
def ES {a : nnreal} (X : s → ℝ) (hX : measurable X) (ha : a ∈ Ioo (0:nnreal) (1:nnreal))
: ennreal  := 
measure.integral (@measure_theory.measure_space.μ ℝ _) (λ h, ennreal.of_real(VaR p hX ha) * Icc_ind a (ennreal.of_real h) )

-- def distribution_function {X : s → ℝ} (hX : measurable X) :=
-- (λ x:ℝ, prob p({ω : s | X(ω) ≤ x}))

-- def unif_df (F : prob_distribution s p) := F.cdf = λ x : ℝ, if (x < 0) then (0:nnreal) else (if (x < 1) then nnreal.of_real x else 0)

/-- Uniformly distributed random variable -/
structure uniform_distribution (s : Type*) [probability_space s](p : probability_measure s) :=
(X : s → ℝ)
(is_rv : measurable X)
(ucdf : distribution_function p is_rv = λ x : ℝ, if (x < 0) then (0:nnreal) else (if (x < 1) then nnreal.of_real x else 0))

def expectation : ennreal := measure.integral (@probability_measure.to_measure s _ p) (λ (ω :s), ennreal.of_real (X ω)) 

-- structure coherent_risk_measure :=
-- (to_fun : )