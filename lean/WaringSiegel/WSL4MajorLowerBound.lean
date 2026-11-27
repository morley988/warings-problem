import WaringSiegel.WSL4MajorBroadApproximation
import WaringSiegel.WSL4MajorPowerCutoff
import WaringSiegel.WSL4MajorCompactPositivity
import WaringSiegel.WSL4PowerSeriesEuler

/-! # Uniform positivity of the original broad major coefficient

The profiles, cutoff exponent, arithmetic constants and norm threshold all
precede the target. All analytic and arithmetic estimates used here concern
the literal sources, measures, coefficients and local eligibility predicate.
-/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem exists_smoothRootMajorLowerBound
    (k n : ℕ) (hk : 3≤k) (hn : 8≤n) (hkn : k+3≤n)
    (hvariables : Thresholds.sufficientVariables k≤(n:ℤ)) (B : ℝ) (hB : 0<B) :
    ∃ ρ R : ℝ, ∃ hρ : 0<ρ, ∃ hR : 0<R,
      SmoothMajorLowerBound (K := K) k n B ρ R hρ hR := by
  have hk0 : 0<k := by omega
  obtain ⟨ρ,R,j,hρ,hR,hj,hSI⟩ := exists_compact_lattice_smooth_singularIntegral
    (K := K) k n hk0 (by omega) B hB
  obtain ⟨v,hv,hSS⟩ := powerIdealSingularSeries_uniform_positive (K := K) k n hk0 hn hkn
  let δ : ℝ := 1/(k:ℝ)
  have hδ : 0<δ := by dsimp [δ]; positivity
  let M := powerUniformSingularSeriesConstant K k
  obtain ⟨a,C₀,η,ha0,ha1,hC₀,hη,hfull⟩ :=
    broadSmoothCoefficient_grouped_main_error (K := K) k n hk (by omega) hvariables ρ R hρ hR δ hδ.le
  obtain ⟨N,hN⟩ := exists_power_cutoff_poisson_order k a ha1
  obtain ⟨C₁,C₂,hC₁,hC₂,herror⟩ := hfull N
  let Q : ℝ := (k:ℝ)^finrank ℚ K
  have hQ : 1≤Q := one_le_pow₀ (by exact_mod_cast (show 1≤k by omega))
  obtain ⟨X0,hX0,hsmall⟩ := exists_power_cutoff_relative_error_small k N Q a δ η
    C₁ (C₂*M) C₀ (v*j/2) hQ ha0 ha1 hδ hη hN (by positivity)
  let D : ℝ := (FractionalIdeal.absNorm (inverseDifferent K):ℝ)
  have hD : 0<D := fractionalIdeal_absNorm_pos _ inverseDifferent_ne_zero
  let T : ℝ := max X0 ((2:ℝ)^finrank ℚ K/D+1)
  have hT1 : 1≤T := hX0.trans (le_max_left _ _)
  have hT : 0<T := lt_of_lt_of_le zero_lt_one hT1
  refine ⟨ρ,R,hρ,hR,v*j/2,T^k,by positivity,by positivity,?_⟩
  intro target htarget hpositive hlocal hsize hregion
  let P := rootScale k target
  let X : ℝ := P^finrank ℚ K
  let L : ℝ := Q*X^a
  let Z : ℝ := majorScale (K := K) k n P
  let S := powerIdealSingularSeries k n target
  let J := pairedWeightedSingularIntegral (integerLatticeSourceScale K) k n
    (smoothRootWeight ρ R) (normalizedTarget k 1 target)
  let A := smoothRootMajorCoefficient k n ρ R hρ hR target htarget
  have hP : 0<P := rootScale_pos htarget k
  have hX : 1≤X := one_le_pow₀ (one_le_rootScale htarget k)
  have hXpos : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hZ : 0<Z := majorScale_pos (K := K) k n P hP
  have hXP : X^k=absNorm target := by
    dsimp [X,P]
    rw [← pow_mul,Nat.mul_comm (finrank ℚ K) k,pow_mul,rootScale_pow k hk0,normScale_pow_degree]
  have hTX : T<X := by
    by_contra h
    have hp := pow_le_pow_left₀ hXpos.le (le_of_not_gt h) k
    rw [hXP] at hp
    linarith
  obtain ⟨hL1,hLX,herrsmall⟩ := hsmall X ((le_max_left _ _).trans_lt hTX)
  have hlarge : (2:ℝ)^finrank ℚ K/D<X := by
    have hh := (le_max_right X0 ((2:ℝ)^finrank ℚ K/D+1)).trans_lt hTX
    linarith
  have hsep := power_cutoff_separated (finrank ℚ K) k hk D X L hD hX
    (le_trans zero_le_one hL1) hLX hlarge
  have hpow : (P^k)^finrank ℚ K=X^k := by
    dsimp [X]
    rw [← pow_mul,← pow_mul,Nat.mul_comm k (finrank ℚ K)]
  rw [← hpow] at hsep
  obtain ⟨hweighted,hbound⟩ := idealPrimitivePowerCoefficient_norm_root_uniform_bound k n hk0 hn hkn target
  have he := herror target htarget M hweighted hbound hL1 hLX hsep
  change ‖A-(Z:ℂ)*(S*J)‖≤
    C₀*X^((n:ℝ)-k-η)+(C₁*P^(finrank ℚ K*n)*(L/X)^N*(1+L/X)+Z*C₂*M/L^δ) at he
  have hfactor :
      C₀*X^((n:ℝ)-k-η)+(C₁*P^(finrank ℚ K*n)*(L/X)^N*(1+L/X)+Z*C₂*M/L^δ) =
      Z*(C₁*(Q^N*X^((k:ℝ)+(N:ℝ)*(a-1))*(1+Q*X^(a-1)))+
        (C₂*M)/(Q*X^a)^δ+C₀/X^η) := by
    have hf := power_cutoff_poisson_factor X Q a hXpos k n N
    have hz : Z=X^((n:ℝ)-k) := rfl
    rw [pow_mul]
    change C₀*X^((n:ℝ)-k-η)+(C₁*X^n*(Q*X^a/X)^N*(1+Q*X^a/X)+Z*C₂*M/(Q*X^a)^δ)=_
    rw [Real.rpow_sub hXpos ((n:ℝ)-k) η]
    have hp : C₁*X^n*(Q*X^a/X)^N*(1+Q*X^a/X)=
      C₁*(X^n*(Q*X^a/X)^N*(1+Q*X^a/X)) := by ring
    rw [hp,hf,hz]
    ring
  rw [hfactor] at he
  have herrorSmall : ‖A-(Z:ℂ)*(S*J)‖<Z*(v*j/2) :=
    he.trans_lt (mul_lt_mul_of_pos_left herrsmall hZ)
  obtain ⟨hjs,hjim⟩ := hSI _ hregion
  obtain ⟨_,hsim,hss⟩ := hSS target htarget hlocal
  have hmain : Z*(v*j)≤((Z:ℂ)*(S*J)).re := by
    change Z*(v*j)≤((Z:ℂ)*(S*J)).re
    rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Complex.mul_re,hsim,zero_mul,sub_zero]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hss hjs hj.le (hv.le.trans hss)) hZ.le
  have hre := Complex.re_le_norm ((Z:ℂ)*(S*J)-A)
  rw [Complex.sub_re,norm_sub_rev] at hre
  change (v*j/2)*X^((n:ℝ)-k)≤A.re
  change (v*j/2)*Z≤A.re
  nlinarith

#print axioms exists_smoothRootMajorLowerBound
end WaringSiegel.WSL4
