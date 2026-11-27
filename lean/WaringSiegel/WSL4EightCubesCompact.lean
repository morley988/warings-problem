import WaringSiegel.WSL4MajorAuxiliaryUniform
import WaringSiegel.WSL4AuxiliaryMinorIntegral
import WaringSiegel.WSL4WeilAuxiliaryPrimeMinor
import WaringSiegel.WSL4WeilRepresentation
import WaringSiegel.WSL4MajorCompactPositivity
import WaringSiegel.WSL3AuxiliaryPositive
import WaringSiegel.WSL2UnitReduction
import WaringSiegel.WSL3MomentRepresentationMajor

/-! # Eight actual positive cubes on a fixed compact normalized target region

All constants precede the target. The auxiliary prime is supplied by Bertrand;
both actual arc coefficients are controlled by proved estimates, and Fourier
nonvanishing produces the literal representation and its required norm bound.
-/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
  WaringSiegel.WSL4 WaringSiegel.WSL4Weil
variable {K : Type*} [Field K] [NumberField K]

theorem compact_eight_cubes_bound (B : ℝ) (hB : 0<B) :
    CompactWaringSiegelBound K 3 8 B := by
  obtain ⟨ρ,R,j,hρ,hR,hj,hSI⟩ := exists_compact_lattice_smooth_singularIntegral
    (K:=K) 3 8 (by norm_num) (by norm_num) B hB
  obtain ⟨v,hv,hSS⟩ := auxiliaryCubicSingularSeries_uniform_positive_173 (K:=K)
  let c : ℝ := v*j/4
  have hc : 0<c := by dsimp [c]; positivity
  obtain ⟨XM,hXM,hmajor⟩ := auxiliaryMajorCoefficient_uniform_approximation
    (K:=K) ρ R hρ hR (auxiliaryBroadConstant K R) (auxiliaryBroadConstant_ge_one R)
    (49/480) (by norm_num) c hc
  obtain ⟨C,hC,hminor⟩ := auxiliaryMinorCoefficient_bound (K:=K)
    ρ R hρ hR (1/100) (by norm_num)
  obtain ⟨XE,hXE,hsmall⟩ := exists_auxiliary_minor_relative_small
    C c (1/100) hC.le hc (by norm_num)
  obtain ⟨P0,hP0,hprime⟩ := exists_auxiliary_cubic_prime_volume (finrank ℚ K)
  let U : ℝ := max P0 (max XM XE)
  have hU1 : 1≤U := hP0.trans (le_max_left _ _)
  have hU : 0<U := lt_of_lt_of_le zero_lt_one hU1
  refine ⟨(2*R)^finrank ℚ K,by positivity,U^(finrank ℚ K*3),by positivity,?_⟩
  intro target hpositive heligible hsize hregion
  have htarget : target≠0 := by
    intro hz
    have hh : 0<absNorm target := (pow_pos hU _).trans hsize
    simpa [hz,absNorm] using hh
  let P := rootScale 3 target
  let X := P^finrank ℚ K
  have hP : 0<P := rootScale_pos htarget 3
  have hP1 : 1≤P := one_le_rootScale htarget 3
  have hX : 0<X := pow_pos hP _
  have hXP : X^3=absNorm target := by
    dsimp [X,P]
    rw [← pow_mul,Nat.mul_comm (finrank ℚ K) 3,pow_mul,
      rootScale_pow 3 (by norm_num),normScale_pow_degree]
  have hPN : P^(finrank ℚ K*3)=absNorm target := by
    rw [pow_mul]
    exact hXP
  have hUP : U<P := by
    by_contra hn
    have hh := pow_le_pow_left₀ hP.le (le_of_not_gt hn) (finrank ℚ K*3)
    rw [hPN] at hh
    exact not_lt_of_ge hh hsize
  have hPX : P≤X := by
    have hd : 1≤finrank ℚ K := finrank_pos (R:=ℚ) (M:=K)
    simpa only [pow_one] using pow_le_pow_right₀ hP1 hd
  have hMX : XM<X :=
    ((le_max_left XM XE).trans (le_max_right P0 (max XM XE))).trans_lt (hUP.trans_le hPX)
  have hEX : XE<X :=
    ((le_max_right XM XE).trans (le_max_right P0 (max XM XE))).trans_lt (hUP.trans_le hPX)
  obtain ⟨p,hp,h173,hlow,hup,h7,hdiv⟩ :=
    hprime P ((le_max_left P0 (max XM XE)).trans_lt hUP)
  let Y := (p:ℝ)^finrank ℚ K
  let z := auxiliaryMajorScale (K:=K) P p
  let S := auxiliaryCubicSingularSeries (p:𝓞 K) (Nat.cast_ne_zero.mpr hp.ne_zero) target
  let J := pairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8
    (smoothRootWeight ρ R) (normalizedTarget 3 1 target)
  let L := auxiliaryBroadConstant K R*X
  let A := auxiliaryMajorCoefficient ρ R hρ hR P hP p hp.pos L target
  let E := auxiliaryMinorCoefficient ρ R hρ hR P hP p hp.pos L target
  have hz : 0<z := auxiliaryMajorScale_pos (K:=K) P hP p hp.pos
  have hMA : ‖A-(z:ℂ)*(S*J)‖≤c*z := hmajor target htarget hMX p hp h173 hup
  have hE : ‖E‖≤C*X^(5+(1/100:ℝ))*Y^(-(9/2):ℝ) :=
    hminor P hP1 p hp h7 target
  have hES : ‖E‖<c*z := by
    have hr : C*X^(5+(1/100:ℝ))*Y^(-(9/2):ℝ)<c*X^5/Y^4 := by
      simpa only [neg_div] using hsmall X hEX Y hlow
    have hh := hE.trans_lt hr
    exact hh.trans_eq (by dsimp [z,auxiliaryMajorScale,X,Y]; ring)
  obtain ⟨hjs,hjim⟩ := hSI _ hregion
  obtain ⟨_,hsim,hss⟩ := hSS target heligible htarget p hp h173
  have hmain : z*(v*j)≤((z:ℂ)*(S*J)).re := by
    rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Complex.mul_re,hsim,zero_mul,sub_zero]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hss hjs hj.le (hv.le.trans hss)) hz.le
  have hreal := Complex.re_le_norm ((z:ℂ)*(S*J)-A)
  rw [Complex.sub_re,norm_sub_rev] at hreal
  have hminorReal := (abs_le.mp (Complex.abs_re_le_norm E)).1
  apply representable_eight_cubes_of_auxiliaryFourier_pos ρ R hρ hR target htarget p hp.pos
  rw [auxiliaryFourier_eq_major_add_minor ρ R hρ hR P hP p hp.pos L target,Complex.add_re]
  change 0<A.re+E.re
  have hcprod : c*z=z*(v*j)/4 := by dsimp [c]; ring
  have hmainpos : 0<z*(v*j) := mul_pos hz (mul_pos hv hj)
  rw [hcprod] at hMA hES
  linarith

#print axioms compact_eight_cubes_bound
end WaringSiegel.WSL4Local
