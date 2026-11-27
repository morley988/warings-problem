import Waring.PolicyCompletionMajorPowerRanges
import Waring.SeedCompletionSourceBounds

/-! # The genuine source major-terminal exponent at every small power cutoff -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.PolicyCompletionMajorSourceBound
open PolicyCompletionMajorPowerRanges PolicyCompletionMajorIntegral
open PolicyCompletionMajorBox PolicyCompletionMajorBoxRanges
open SeedCompletionSourceBounds CartesianFloorScales NormalizedCoefficient SmoothMoments

def majorSourceExponent {j : ℕ} (k s : ℕ) (φ : Fin j → ℝ) (Δ : ℝ) : ℝ :=
  amplitude k φ+(1-total φ)*(((2*s:ℕ):ℝ)-(k:ℝ))+
    max 0 (2*Δ/(k:ℝ)-1/((k-j:ℕ):ℝ))

theorem major_source_power_bound {k j s : ℕ} (hk : 1≤k) (hj : j+2≤k) (hs : 1≤s)
    {D : ℝ} (hD : 1≤D) (φ : Fin j → ℝ) (hφ : ∀ i,0≤φ i)
    (hh : ∀ i,0<shiftExponents k φ i) {Δ : ℝ}
    (hadm : AdmissibleExcess k (2*s) Δ) :
    SourcePowerBound
      (fun P R => boxMajorIntegral k s (D*P) P R (fun i => P^(φ i)))
      (majorSourceExponent k s φ Δ) := by
  intro ε hε
  let δ : ℝ := ε/2
  have hδ : 0<δ := by dsimp [δ]; positivity
  let q : ℝ := 1-total φ
  have hq : 0<q := length_pos (by omega) φ (fun i => (hh i).le)
  let b : ℝ := ((2*s:ℕ):ℝ)-(k:ℝ)
  let gap : ℝ := max 0 (2*Δ/(k:ℝ)-1/((k-j:ℕ):ℝ))
  obtain ⟨ηg,hηg,C₀,hC₀,hbound⟩ := source_box_major_integral hk hj hs hadm hδ
  let η₀ := min (q*ηg) (ε/(2*((j:ℝ)+1)))
  have hη₀ : 0<η₀ := lt_min (mul_pos hq hηg) (div_pos hε (by positivity))
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηle
  have hηg' : η≤q*ηg := hηle.trans (min_le_left _ _)
  have hηj : η*(j:ℝ)≤δ := by
    have hη' := hηle.trans (min_le_right (q*ηg) (ε/(2*((j:ℝ)+1))))
    have hmul := (le_div_iff₀ (by positivity : (0:ℝ)<2*((j:ℝ)+1))).mp hη'
    dsimp [δ]
    nlinarith
  let threshold := max 1 (majorSmoothnessThreshold k j)
  have hthreshold : 0<threshold := zero_lt_one.trans_le (le_max_left _ _)
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  let P₀ := max (coordinateThreshold (shiftExponents k φ)) (threshold^(1/(η*(k:ℝ))))
  let C : ℝ := C₀*D^(δ+gap)*D*D^j*D^b
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,P₀,(coordinateThreshold_ge_one _).trans (le_max_left _ _),?_⟩
  intro P hPP
  have hPthreshold : coordinateThreshold (shiftExponents k φ)≤P := (le_max_left _ _).trans hPP
  have hP : 1≤P := (coordinateThreshold_ge_one _).trans hPthreshold
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hR : 1≤P^η := Real.one_le_rpow hP hη.le
  have hL : 1≤D*P := one_le_mul_of_one_le_of_one_le hD hP
  have hM : ∀ i,1≤P^(φ i) := fun i => Real.one_le_rpow hP (hφ i)
  have hH : ∀ i,2≤boxHeights k (D*P) (fun i => P^(φ i)) i :=
    power_height_lower k hD φ hh hPthreshold
  have hY : 1≤boxSmoothLength (D*P) (fun i => P^(φ i)) := by
    rw [boxSmoothLength_power hPp D φ hφ]
    exact one_le_mul_of_one_le_of_one_le hD (Real.one_le_rpow hP hq.le)
  have hRY : P^η≤(boxSmoothLength (D*P) (fun i => P^(φ i)))^ηg := by
    rw [boxSmoothLength_power hPp D φ hφ]
    calc
      _ ≤ P^(q*ηg) := Real.rpow_le_rpow_of_exponent_le hP hηg'
      _ = (P^q)^ηg := Real.rpow_mul hPp.le q ηg
      _ ≤ (D*P^q)^ηg := Real.rpow_le_rpow (Real.rpow_nonneg hPp.le _)
        (le_mul_of_one_le_left (Real.rpow_nonneg hPp.le _) hD) hηg.le
  have hlarge : majorSmoothnessThreshold k j≤(P^η)^k := by
    have hp := fixed_constant_rpow_bound hthreshold (mul_pos hη hkR)
      ((le_max_right _ _).trans hPP)
    apply (le_max_right 1 (majorSmoothnessThreshold k j)).trans
    simpa only [← Real.rpow_mul_natCast hPp.le] using hp
  have hRj : (P^η)^j≤P^δ := by
    rw [← Real.rpow_mul_natCast hPp.le]
    exact Real.rpow_le_rpow_of_exponent_le hP hηj
  have hraw := hbound (D*P) P (P^η) (fun i => P^(φ i)) hL hR hM hH hY hRY hlarge
  have hnon : 0≤boxMajorIntegral k s (D*P) P (P^η) (fun i => P^(φ i)) :=
    integral_nonneg (fun α => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) (2*s)))
  rw [abs_of_nonneg hnon]
  apply hraw.trans
  rw [boxHeightProduct_power k hPp D φ (fun i => (hh i).le),
    power_parameters_product hPp φ hφ,boxSmoothLength_power hPp D φ hφ]
  change C₀*(D*P)^(δ+gap)*(D*P)*(D^j*P^((j:ℝ)-(k:ℝ)*total φ))*P^(total φ)*(P^η)^j*
    (D*P^q)^b≤C*P^(majorSourceExponent k s φ Δ+ε)
  calc
    _ ≤ C₀*(D*P)^(δ+gap)*(D*P)*(D^j*P^((j:ℝ)-(k:ℝ)*total φ))*P^(total φ)*P^δ*(D*P^q)^b := by
      gcongr
    _ = C*(P^(δ+gap)*P*P^((j:ℝ)-(k:ℝ)*total φ)*P^(total φ)*P^δ*P^(q*b)) := by
      rw [Real.mul_rpow hDp.le hPp.le,Real.mul_rpow hDp.le (Real.rpow_nonneg hPp.le _),
        ← Real.rpow_mul hPp.le]
      dsimp [C]
      ring
    _ = _ := by
      congr 1
      calc
        _ = P^(δ+gap)*P^(1:ℝ)*P^((j:ℝ)-(k:ℝ)*total φ)*P^(total φ)*P^δ*P^(q*b) := by
          rw [Real.rpow_one]
        _ = P^((δ+gap)+1+((j:ℝ)-(k:ℝ)*total φ)+total φ+δ+q*b) := by
          repeat' rw [← Real.rpow_add hPp]
        _ = _ := by
          congr 1
          dsimp [δ,majorSourceExponent,amplitude,q,b,gap]
          ring

#print axioms major_source_power_bound
end Waring.PolicyCompletionMajorSourceBound
