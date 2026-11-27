import WaringSiegel.WSL4MajorQuadraticUniform
import WaringSiegel.WSL4MajorCompactPositivity
import WaringSiegel.WSL2UnitReduction

/-! # The literal quadratic local-conditional theorem at 256 variables -/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem compact_quadratic_local_bound (B : ℝ) (hB : 0<B) :
    CompactLocalConditionalBound K 2 256 B := by
  obtain ⟨ρ,R,j,hρ,hR,hj,hSI⟩ := exists_compact_lattice_smooth_singularIntegral
    (K := K) 2 256 (by norm_num) (by norm_num) B hB
  obtain ⟨v,hv,hSS⟩ := powerIdealSingularSeries_uniform_positive
    (K := K) 2 256 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨X0,hX0,happrox⟩ := quadraticSmoothFullCoefficient_uniform_approximation
    (K := K) ρ R hρ hR (v*j/2) (by positivity)
  have hX0p : 0<X0 := lt_of_lt_of_le zero_lt_one hX0
  refine ⟨(2*R)^finrank ℚ K,by positivity,X0^2,by positivity,?_⟩
  intro target hpositive hlocal hsize hregion
  have htarget : target≠0 := by
    intro hz
    have hn : 0<absNorm target := (pow_pos hX0p 2).trans hsize
    simpa [hz,absNorm] using hn
  let P := rootScale 2 target
  let X := P^finrank ℚ K
  let Z := majorScale (K := K) 2 256 P
  let S := powerIdealSingularSeries 2 256 target
  let J := pairedWeightedSingularIntegral (integerLatticeSourceScale K) 2 256
    (smoothRootWeight ρ R) (normalizedTarget 2 1 target)
  let A := quadraticSmoothFullCoefficient ρ R hρ hR target htarget
  have hP : 0<P := rootScale_pos htarget 2
  have hX : 0<X := pow_pos hP _
  have hZ : 0<Z := majorScale_pos (K := K) 2 256 P hP
  have hXP : X^2=absNorm target := by
    dsimp [X,P]
    rw [← pow_mul,Nat.mul_comm (finrank ℚ K) 2,pow_mul,
      rootScale_pow 2 (by norm_num),normScale_pow_degree]
  have hlarge : X0<X := by
    by_contra h
    have hh := pow_le_pow_left₀ hX.le (le_of_not_gt h) 2
    rw [hXP] at hh
    linarith
  have he := happrox target htarget hlarge
  obtain ⟨hjs,hjim⟩ := hSI _ hregion
  obtain ⟨_,hsim,hss⟩ := hSS target htarget hlocal
  have hmain : Z*(v*j)≤((Z:ℂ)*(S*J)).re := by
    rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Complex.mul_re,hsim,zero_mul,sub_zero]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hss hjs hj.le (hv.le.trans hss)) hZ.le
  have hre := Complex.re_le_norm ((Z:ℂ)*(S*J)-A)
  rw [Complex.sub_re,norm_sub_rev] at hre
  apply representable_of_smoothRootFourier_pos 2 256 (by norm_num) target htarget ρ R hρ hR
  change 0<A.re
  change ‖A-(Z:ℂ)*(S*J)‖≤(v*j/2)*Z at he
  nlinarith [mul_pos hZ (mul_pos hv hj)]

theorem quadratic_localConditionalBound (K : Type*) [Field K] [NumberField K] :
    LocalConditionalBound K 2 256 := by
  obtain ⟨B,hB,_,hreduce⟩ := exists_compact_local_reduction K 2 (by norm_num)
  exact (hreduce 256).mp (compact_quadratic_local_bound B (lt_of_lt_of_le zero_lt_one hB))

#print axioms compact_quadratic_local_bound
#print axioms quadratic_localConditionalBound
end WaringSiegel.WSL4
