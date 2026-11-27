import WaringSiegel.WSL4MajorMass
import WaringSiegel.WSL4MajorScaling
import WaringSiegel.WSL3UnitFrequencyTails
import WaringSiegel.WSL3PoissonMixedTrivial

/-! # Actual integrated all-degree small-arc Poisson replacement

This replaces the literal smooth trace source by the genuine zero-dual
Poisson term on every separated union with L <= P^d.  The error retains an
arbitrary positive power of L/P^d and is uniform in the target.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.mixedEmbedding Module
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators Pointwise ENNReal
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem smoothPowerCenterMainTerm_continuous (k : ℕ) (ρ R : ℝ)
    (hρ : 0<ρ) (hR : 0<R) (P : ℝ) (γ : K) :
    Continuous (smoothPowerCenterMainTerm k ρ R P γ) := by
  unfold smoothPowerCenterMainTerm
  exact continuous_const.smul (continuous_const.mul
    ((weightedRootIntegral_continuous k ρ R hρ hR).comp (continuous_const.smul continuous_id)))

local instance replacementCentersFintype (N : ℕ) : Fintype (traceRationalCenters K N) :=
  Fintype.ofFinite _

def smoothMajorMainIntegral (k n : ℕ) (ρ R P L : ℝ) (target : 𝓞 K) : ℂ :=
  ∑ q : traceRationalCenters K ⌊L⌋₊,
    ∫ β in centeredTraceArc (P^k) L (traceCenterRepresentative q),
      smoothPowerCenterMainTerm k ρ R P (traceCenterRepresentative q) β ^ n *
        traceTorusCharacter (-target)
          (Submodule.Quotient.mk (mixedEmbedding K (traceCenterRepresentative q)+β))
      ∂archimedeanDualMeasure (integerLatticeSourceScale K)

theorem smoothMajorMainIntegral_rootScale_formula
    (k n : ℕ) (hk : 0<k) (ρ R L : ℝ) (target : 𝓞 K) (htarget : target≠0) :
    smoothMajorMainIntegral k n ρ R (rootScale k target) L target =
      (majorScale (K := K) k n (rootScale k target) : ℂ) *
        ∑ q : traceRationalCenters K ⌊L⌋₊,
          majorCompleteCoefficient k n target (traceCenterRepresentative q) *
            productSingularIntegral k n ρ R
              (L/((traceConductor (traceCenterRepresentative q)).absNorm:ℝ))
              (normalizedTarget k 1 target) := by
  simp only [smoothMajorMainIntegral,
    smoothPowerCenterMainTerm_integral k n hk ρ R L target htarget,Finset.mul_sum,mul_assoc]

/-- An actual small-major-arc replacement estimate, with no exponential-sum
or integral estimate retained as a hypothesis. -/
theorem smoothMajor_poisson_replacement
    (k s : ℕ) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 0<P) (L : ℝ), 0≤L → L≤P^(finrank ℚ K) →
      (2:ℝ)^(finrank ℚ K)*L^2 <
        (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*(P^k)^(finrank ℚ K) →
      ∀ target : 𝓞 K,
        ‖(∫ q in traceMajorArcUnion (P^k) L,
            smoothTraceIntegrand k (s+1) ρ R hρ hR P hP.ne' target q ∂traceHaar)-
          smoothMajorMainIntegral k (s+1) ρ R P L target‖ ≤
          C*P^(finrank ℚ K*(s+1))*(L/P^(finrank ℚ K))^N*(1+L/P^(finrank ℚ K)) := by
  obtain ⟨C,hC,herror⟩ := smoothPower_center_power_main_error (K := K) k s ρ R hρ hR N
  refine ⟨C,hC,?_⟩
  intro P hP L hL hLP hsmall target
  apply centeredArcIntegral_error_le (P^k) L (pow_pos hP _) hL hsmall
    (smoothTraceIntegrand k (s+1) ρ R hρ hR P hP.ne' target)
    (smoothTraceIntegrand_continuous _ _ _ _ _ _ _ _ _)
    (fun q β => smoothPowerCenterMainTerm k ρ R P (traceCenterRepresentative q) β^(s+1) *
      traceTorusCharacter (-target)
        (Submodule.Quotient.mk (mixedEmbedding K (traceCenterRepresentative q)+β)))
  · intro q
    exact ((smoothPowerCenterMainTerm_continuous k ρ R hρ hR P _).pow (s+1)).mul
      ((traceTorusCharacter_continuous (-target)).comp
        (continuous_quotient_mk'.comp (continuous_const.add continuous_id)))
  · positivity
  · intro q β hβ
    dsimp only [smoothTraceIntegrand]
    rw [smoothTraceSource_center_eq,← sub_mul,norm_mul,traceTorusCharacter_norm_one,mul_one]
    have ha0 := powerArcRatio_nonneg k P hP β (traceConductor (traceCenterRepresentative q))
    have ha : powerArcRatio k P β (traceConductor (traceCenterRepresentative q)) ≤
        L/P^(finrank ℚ K) := div_le_div_of_nonneg_right hβ (pow_nonneg hP.le _)
    have ha1 : powerArcRatio k P β (traceConductor (traceCenterRepresentative q)) ≤ 1 :=
      ha.trans ((div_le_one (pow_pos hP _)).mpr hLP)
    apply (herror (traceCenterRepresentative q) P hP β ha1).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 ha N) (by positivity)
    · linarith
    · linarith
    · positivity

#print axioms smoothMajorMainIntegral_rootScale_formula
#print axioms smoothMajor_poisson_replacement
end WaringSiegel.WSL4
