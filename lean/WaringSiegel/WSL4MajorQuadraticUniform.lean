import WaringSiegel.WSL4MajorQuadraticSaving
import WaringSiegel.WSL4MajorGroupedApproximation
import WaringSiegel.WSL4MajorPowerCutoff
import WaringSiegel.WSL4PowerSeriesEuler

/-! # Full quadratic coefficient asymptotics at 256 variables -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module Filter
open scoped BigOperators Classical NumberField SchwartzMap Topology
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local
variable {K : Type*} [Field K] [NumberField K]

def quadraticSmoothFullCoefficient (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (target : 𝓞 K) (htarget : target≠0) : ℂ :=
  ∫ q, smoothTraceSource 2 ρ R hρ hR (rootScale 2 target) (rootScale_pos htarget 2).ne' q^256 *
    traceTorusCharacter (-target) q ∂traceHaar

theorem exists_quadratic_cutoff_separated (d : ℕ) (D Q : ℝ) (hD : 0<D) :
    ∃ T : ℝ, 1≤T ∧ ∀ X : ℝ, T<X →
      (2:ℝ)^d*(Q*X^((2:ℝ)/3))^2<D*X^2 := by
  have hev := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/3)).eventually_gt_atTop
    ((2:ℝ)^d*Q^2/D)
  obtain ⟨T,hT⟩ := eventually_atTop.mp hev
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro X hX
  have hX0 : 0<X := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hX.le)
  have hh := hT X ((le_max_right _ _).trans hX.le)
  have hcoef : (2:ℝ)^d*Q^2<D*X^((2:ℝ)/3) := by
    simpa only [mul_comm] using (div_lt_iff₀ hD).mp hh
  have hsq : (X^((2:ℝ)/3))^2=X^((4:ℝ)/3) := by
    rw [← Real.rpow_mul_natCast hX0.le]
    norm_num
  have hprod : X^((2:ℝ)/3)*X^((4:ℝ)/3)=X^2 := by
    rw [← Real.rpow_add hX0]
    norm_num
  calc
    _ = ((2:ℝ)^d*Q^2)*X^((4:ℝ)/3) := by rw [mul_pow,hsq]; ring
    _ < (D*X^((2:ℝ)/3))*X^((4:ℝ)/3) :=
      mul_lt_mul_of_pos_right hcoef (Real.rpow_pos_of_pos hX0 _)
    _ = _ := by rw [mul_assoc,hprod]

theorem quadraticSmoothFullCoefficient_uniform_approximation
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (c : ℝ) (hc : 0<c) :
    ∃ X0 : ℝ, 1≤X0 ∧ ∀ (target : 𝓞 K) (htarget : target≠0),
      X0<(rootScale 2 target)^finrank ℚ K →
      ‖quadraticSmoothFullCoefficient ρ R hρ hR target htarget-
        (majorScale (K := K) 2 256 (rootScale 2 target):ℂ)*
          (powerIdealSingularSeries 2 256 target *
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) 2 256
              (smoothRootWeight ρ R) (normalizedTarget 2 1 target))‖ ≤
        c*majorScale (K := K) 2 256 (rootScale 2 target) := by
  obtain ⟨C₀,hC₀,hminor⟩ := quadratic_smooth_full_sub_cutoff_bound (K := K) ρ R hρ hR
  obtain ⟨C₁,C₂,hC₁,hC₂,hmajor⟩ := narrowSmoothCoefficient_grouped_main_error (K := K)
    2 255 (by norm_num) ρ R hρ hR (1/2) (by norm_num) 9
  let Q : ℝ := (2:ℝ)^finrank ℚ K
  have hQ : 1≤Q := one_le_pow₀ (by norm_num)
  let M := powerUniformSingularSeriesConstant K 2
  obtain ⟨X0,hX0,hsmall⟩ := exists_power_cutoff_relative_error_small 2 9 Q (2/3) (1/2) 1
    C₁ (C₂*M) C₀ c hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc
  let D : ℝ := (FractionalIdeal.absNorm (inverseDifferent K):ℝ)
  have hD : 0<D := fractionalIdeal_absNorm_pos _ inverseDifferent_ne_zero
  obtain ⟨T,hT,hseparate⟩ := exists_quadratic_cutoff_separated (finrank ℚ K) D Q hD
  refine ⟨max X0 T,hX0.trans (le_max_left _ _),?_⟩
  intro target htarget hsize
  let P := rootScale 2 target
  let X := P^finrank ℚ K
  let L := Q*X^((2:ℝ)/3)
  let Z := majorScale (K := K) 2 256 P
  let A := quadraticSmoothFullCoefficient ρ R hρ hR target htarget
  let B := cutoffSmoothCoefficient 2 256 ρ R hρ hR L target htarget
  let S := powerIdealSingularSeries 2 256 target *
    pairedWeightedSingularIntegral (integerLatticeSourceScale K) 2 256
      (smoothRootWeight ρ R) (normalizedTarget 2 1 target)
  have hP : 0<P := rootScale_pos htarget 2
  have hX : 0<X := pow_pos hP _
  have hZ : 0<Z := majorScale_pos (K := K) 2 256 P hP
  obtain ⟨hL1,hLX,herr⟩ := hsmall X ((le_max_left _ _).trans_lt hsize)
  have hsep := hseparate X ((le_max_right _ _).trans_lt hsize)
  have hpow : (P^2)^finrank ℚ K=X^2 := by
    dsimp [X]
    rw [← pow_mul,← pow_mul,Nat.mul_comm 2]
  rw [← hpow] at hsep
  obtain ⟨hweighted,hbound⟩ := idealPrimitivePowerCoefficient_norm_root_uniform_bound
    2 256 (by norm_num) (by norm_num) (by norm_num) target
  have h1 := hminor target htarget
  have h2 := hmajor target htarget M hweighted hbound L hL1 hLX hsep
  have he : ‖A-(Z:ℂ)*S‖≤ C₀*X^((253:ℝ)) +
      (C₁*P^(finrank ℚ K*256)*(L/X)^9*(1+L/X)+Z*C₂*M/L^((1:ℝ)/2)) := by
    calc
      _ = ‖(A-B)+(B-(Z:ℂ)*S)‖ := by congr 1; ring
      _ ≤ ‖A-B‖+‖B-(Z:ℂ)*S‖ := norm_add_le _ _
      _ ≤ _ := add_le_add h1 h2
  have hfactor : C₀*X^((253:ℝ)) +
      (C₁*P^(finrank ℚ K*256)*(L/X)^9*(1+L/X)+Z*C₂*M/L^((1:ℝ)/2)) =
      Z*(C₁*(Q^9*X^((2:ℝ)+9*((2:ℝ)/3-1))*(1+Q*X^((2:ℝ)/3-1)))+
        (C₂*M)/(Q*X^((2:ℝ)/3))^((1:ℝ)/2)+C₀/X^(1:ℝ)) := by
    have hf := power_cutoff_poisson_factor X Q ((2:ℝ)/3) hX 2 256 9
    have hz : Z=X^((256:ℝ)-2) := rfl
    rw [pow_mul]
    change C₀*X^((253:ℝ)) +
      (C₁*X^256*(Q*X^((2:ℝ)/3)/X)^9*(1+Q*X^((2:ℝ)/3)/X)+
        Z*C₂*M/(Q*X^((2:ℝ)/3))^((1:ℝ)/2))=_
    rw [show (253:ℝ)=(256-2)-1 by norm_num,Real.rpow_sub hX]
    have ha : C₁*X^256*(Q*X^((2:ℝ)/3)/X)^9*(1+Q*X^((2:ℝ)/3)/X)=
        C₁*(X^256*(Q*X^((2:ℝ)/3)/X)^9*(1+Q*X^((2:ℝ)/3)/X)) := by ring
    rw [ha,hf,hz]
    ring
  rw [hfactor] at he
  exact (he.trans_lt (mul_lt_mul_of_pos_left herr hZ)).le.trans_eq (mul_comm Z c)

#print axioms quadraticSmoothFullCoefficient_uniform_approximation
end WaringSiegel.WSL4
