import Waring.PolicyCompletionMajorIntegral
import Waring.FixedCoefficientPhase

/-! # Exact power-scale identities for the literal auxiliary source boxes -/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionMajorPowerRanges
open PolicyCompletionMajorBoxRanges PolicyCompletionMajorIntegral CartesianFloorScales

def total {j : ℕ} (φ : Fin j → ℝ) : ℝ := ∑ i,φ i

def shiftExponents {j : ℕ} (k : ℕ) (φ : Fin j → ℝ) (i : Fin j) : ℝ := 1-(k:ℝ)*φ i

def amplitude {j : ℕ} (k : ℕ) (φ : Fin j → ℝ) : ℝ := 1+(j:ℝ)-(k:ℝ)*total φ+total φ

theorem shiftExponents_sum {j : ℕ} (k : ℕ) (φ : Fin j → ℝ) :
    (∑ i,shiftExponents k φ i)=(j:ℝ)-(k:ℝ)*total φ := by
  simp only [shiftExponents,total,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one,Finset.mul_sum]

theorem length_pos {k j : ℕ} (hj : j<k) (φ : Fin j → ℝ)
    (hh : ∀ i,0≤shiftExponents k φ i) : 0<1-total φ := by
  have hs : 0≤∑ i,shiftExponents k φ i := Finset.sum_nonneg (fun i _ => hh i)
  rw [shiftExponents_sum] at hs
  have hjR : (j:ℝ)<k := by exact_mod_cast hj
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  nlinarith

theorem power_parameters_product {j : ℕ} {P : ℝ} (hP : 0<P)
    (φ : Fin j → ℝ) (hφ : ∀ i,0≤φ i) : (∏ i,P^(φ i))=P^(total φ) :=
  (Real.rpow_sum_of_nonneg hP.le (fun i _ => hφ i)).symm

theorem boxHeights_power {j : ℕ} (k : ℕ) {P : ℝ} (hP : 0<P)
    (D : ℝ) (φ : Fin j → ℝ) (i : Fin j) :
    boxHeights k (D*P) (fun i => P^(φ i)) i=D*P^(shiftExponents k φ i) := by
  unfold boxHeights shiftExponents
  rw [← Real.rpow_mul_natCast hP.le,Real.rpow_sub hP,Real.rpow_one]
  have hmul : φ i*(k:ℝ)=(k:ℝ)*φ i := mul_comm _ _
  rw [hmul]
  ring

theorem boxHeightProduct_power {j : ℕ} (k : ℕ) {P : ℝ} (hP : 0<P)
    (D : ℝ) (φ : Fin j → ℝ) (hh : ∀ i,0≤shiftExponents k φ i) :
    (∏ i,boxHeights k (D*P) (fun i => P^(φ i)) i)=D^j*P^((j:ℝ)-(k:ℝ)*total φ) := by
  simp_rw [boxHeights_power k hP D φ]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ← Real.rpow_sum_of_nonneg hP.le (fun i _ => hh i),shiftExponents_sum]

theorem boxSmoothLength_power {j : ℕ} {P : ℝ} (hP : 0<P)
    (D : ℝ) (φ : Fin j → ℝ) (hφ : ∀ i,0≤φ i) :
    boxSmoothLength (D*P) (fun i => P^(φ i))=D*P^(1-total φ) := by
  unfold boxSmoothLength
  rw [power_parameters_product hP φ hφ,Real.rpow_sub hP,Real.rpow_one]
  ring

theorem boxConductor_power {j : ℕ} (k : ℕ) {P : ℝ} (hP : 0<P)
    (D : ℝ) (φ : Fin j → ℝ) (hφ : ∀ i,0≤φ i) :
    boxConductor k (D*P) (fun i => P^(φ i))=D^k*P^((k:ℝ)*(1-total φ)) := by
  rw [boxConductor_eq_smoothLength,boxSmoothLength_power hP D φ hφ,mul_pow,
    ← Real.rpow_mul_natCast hP.le]
  congr 2
  ring

theorem power_height_lower {j : ℕ} (k : ℕ) {D P : ℝ} (hD : 1≤D)
    (φ : Fin j → ℝ) (hh : ∀ i,0<shiftExponents k φ i)
    (hP : coordinateThreshold (shiftExponents k φ)≤P) (i : Fin j) :
    2≤boxHeights k (D*P) (fun i => P^(φ i)) i := by
  have hP1 : 1≤P := (coordinateThreshold_ge_one _).trans hP
  rw [boxHeights_power k (zero_lt_one.trans_le hP1)]
  exact (coordinate_powers_ge_two _ hh hP i).trans
    (le_mul_of_one_le_left (Real.rpow_nonneg (zero_le_one.trans hP1) _) hD)

#print axioms length_pos
#print axioms boxHeightProduct_power
#print axioms boxConductor_power
end Waring.PolicyCompletionMajorPowerRanges
