import Waring.SeedCompletionPaddedSecondPower

/-! # Fourth and eighth source moments from actual padded energies -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionPaddedSource
open SeedCompletionSourceBounds SeedCompletionNaturalBox
open PolicyCompletionMajorPowerRanges PolicyCompletionMajorBoxRanges

theorem padded_double_power {k j r s : ℕ} {D a b : ℝ} (hD : 1≤D)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i)
    (hcur : SourcePowerBound (paddedMoment k r s D φ) a)
    (hnext : SourcePowerBound (paddedMoment k (r+1) s (2*D) φ) b) :
    SourcePowerBound (paddedMoment k r (2*s) D φ)
      (max ((1+2*(parameterExponent k φ+(r:ℝ)))*(s:ℝ)+a)
        (2*(s:ℝ)*(parameterExponent k φ+(r:ℝ))+b)) := by
  have hN : SourcePowerBound (fun P _=>(⌊D*P⌋₊ : ℝ)) 1 := by
    simpa [naturalCenters,Int.card_Icc] using powerCentersCard_power hD
  have hC := paddedCard_power r hD φ hφ hshift
  have hA := (((constant 2).mul hN).mul (hC.natPow 2)).natPow s
  have hB := ((constant 4).mul hC).natPow (2*s)
  have H := (hA.mul hcur).add (hB.mul hnext)
  have hF := H.of_le (fun P R _ _=>paddedMoment_nonneg ..)
    (fun P R hP _=>padded_moment_double k r s φ (zero_lt_one.trans_le hD)
      (zero_lt_one.trans_le hP))
  convert hF using 1 <;> push_cast <;> congr 1 <;> ring

theorem padded_fourth_power_of_seconds {k j r : ℕ} {D δ : ℝ} (hD : 1≤D)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i)
    (hcur : SourcePowerBound (paddedMoment k r 1 D φ)
      (1+parameterExponent k φ+(r:ℝ)+δ))
    (hnext : SourcePowerBound (paddedMoment k (r+1) 1 (2*D) φ)
      (1+parameterExponent k φ+((r+1:ℕ):ℝ)+δ)) :
    SourcePowerBound (paddedMoment k r 2 D φ)
      (2+3*(parameterExponent k φ+(r:ℝ))+δ) := by
  have H := padded_double_power hD φ hφ hshift hcur hnext
  norm_num only [Nat.cast_add,Nat.cast_one,mul_one] at H
  have h₁ : 1+2*(parameterExponent k φ+(r:ℝ))+(1+parameterExponent k φ+(r:ℝ)+δ)=
      2+3*(parameterExponent k φ+(r:ℝ))+δ := by ring
  have h₂ : 2*(parameterExponent k φ+(r:ℝ))+(1+parameterExponent k φ+((r:ℝ)+1)+δ)=
      2+3*(parameterExponent k φ+(r:ℝ))+δ := by ring
  simpa only [h₁,h₂,max_self] using H

theorem padded_eighth_power_of_fourths {k j r : ℕ} {D δ : ℝ} (hD : 1≤D)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i)
    (hcur : SourcePowerBound (paddedMoment k r 2 D φ)
      (2+3*(parameterExponent k φ+(r:ℝ))+δ))
    (hnext : SourcePowerBound (paddedMoment k (r+1) 2 (2*D) φ)
      (2+3*(parameterExponent k φ+((r+1:ℕ):ℝ))+δ)) :
    SourcePowerBound (paddedMoment k r 4 D φ)
      (5+7*(parameterExponent k φ+(r:ℝ))+δ) := by
  have H := padded_double_power hD φ hφ hshift hcur hnext
  norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at H
  apply H.weaken
  apply max_le
  · linarith
  · linarith

theorem padded_fourth_power {k j r : ℕ} (hk : k≤18) (hjk : j+(r+1)<k)
    (hj : 1≤j) (hJ : 2≤(k-(j+(r+1)))/2) (hjJ : j≤(k-(j+(r+1)))/2+1)
    {D : ℝ} (hD : 1≤D) (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i)
    (hφ1 : ∀ i,φ i≤1) (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (paddedMoment k r 2 D φ)
      (2+3*(parameterExponent k φ+(r:ℝ))+curveLoss φ) := by
  have hmon : (k-(j+(r+1)))/2≤(k-(j+r))/2 := Nat.div_le_div_right (by omega)
  apply padded_fourth_power_of_seconds hD φ hφ hshift
  · exact padded_second_power hk (by omega) hj (hJ.trans hmon)
      (hjJ.trans (by omega)) hD φ hφ hφ1 hshift
  · exact padded_second_power hk hjk hj hJ hjJ (by linarith) φ hφ hφ1 hshift

theorem padded_eighth_power {k j r : ℕ} (hk : k≤18) (hjk : j+(r+2)<k)
    (hj : 1≤j) (hJ : 2≤(k-(j+(r+2)))/2) (hjJ : j≤(k-(j+(r+2)))/2+1)
    {D : ℝ} (hD : 1≤D) (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i)
    (hφ1 : ∀ i,φ i≤1) (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (paddedMoment k r 4 D φ)
      (5+7*(parameterExponent k φ+(r:ℝ))+curveLoss φ) := by
  have hmon : (k-(j+(r+2)))/2≤(k-(j+(r+1)))/2 := Nat.div_le_div_right (by omega)
  apply padded_eighth_power_of_fourths hD φ hφ hshift
  · exact padded_fourth_power hk (by omega) hj (hJ.trans hmon)
      (hjJ.trans (by omega)) hD φ hφ hφ1 hshift
  · exact padded_fourth_power hk (by omega) hj (by simpa [Nat.add_assoc] using hJ)
      (by simpa [Nat.add_assoc] using hjJ) (by linarith) φ hφ hφ1 hshift

#print axioms padded_fourth_power
#print axioms padded_eighth_power
end Waring.SeedCompletionPaddedSource
