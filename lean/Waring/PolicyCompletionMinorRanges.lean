import Waring.PolicyCompletionMajorPowerRanges
import Waring.AuxiliaryMinorHeights

/-! # Exact minor-height coordinates for the dilated source family -/
noncomputable section
namespace Waring.PolicyCompletionMinorRanges
open AuxiliaryMajorArcs AuxiliaryMinorHeights BasicMatching RationalHeight
open PolicyCompletionMajorBoxRanges PolicyCompletionMajorPowerRanges

theorem source_minor_at_base {k j : ℕ} (hk : 1≤k) {D P R α : ℝ}
    (hD : 1≤D) (hP : 0<P) (φ : Fin j→ℝ) (hφ : ∀i,0≤φ i)
    (hminor : ¬MajorAtCutoff (D*P)
      ((boxConductor k (D*P) (fun i=>P^(φ i))/(D*P))*R^((k*(k-j):ℕ):ℝ)) α) :
    MinorAtCutoff P
      (((D^k/D)*P^((k:ℝ)*(1-total φ))/P)*R^((k*(k-j):ℕ):ℝ)) α := by
  have hm : MinorAtCutoff (D*P)
      ((boxConductor k (D*P) (fun i=>P^(φ i))/(D*P))*R^((k*(k-j):ℕ):ℝ)) α := by
    rw [major_iff_not_minor] at hminor
    exact not_not.mp hminor
  rw [boxConductor_power k hP D φ hφ] at hm
  have heq : D^k*P^((k:ℝ)*(1-total φ))/(D*P)=
      (D^k/D)*P^((k:ℝ)*(1-total φ))/P := by ring
  rw [heq] at hm
  intro r hr
  exact (le_mul_of_one_le_left hP.le hD).trans_lt (hm r hr)

theorem source_minor_normalized_bounds {k j : ℕ} (hk : 1≤k) {D P R η : ℝ}
    (hD : 1≤D) (hP : 1<P) (hR : 1≤R) (hRP : R≤P^η)
    (φ : Fin j→ℝ) (hφ : ∀i,0≤φ i) (hq : 0≤1-total φ)
    (hscale : D^k/D≤P^η) {α : ℝ}
    (hminor : ¬MajorAtCutoff (D*P)
      ((boxConductor k (D*P) (fun i=>P^(φ i))/(D*P))*R^((k*(k-j):ℕ):ℝ)) α) :
    1-(((k*(k-j):ℕ):ℝ)+1)*η<normalizedHeight P (P^((k:ℝ)*(1-total φ))) α ∧
      normalizedHeight P (P^((k:ℝ)*(1-total φ))) α≤(k:ℝ)*(1-total φ)/2 := by
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hc : 1≤D^k/D := by
    apply (le_div_iff₀ hDp).mpr
    simpa only [one_mul,pow_one] using pow_le_pow_right₀ hD hk
  have hm := source_minor_at_base hk hD (zero_lt_one.trans hP) φ hφ hminor
  have hh := minor_normalized_bounds hP hR hRP (mul_nonneg (Nat.cast_nonneg k) hq)
    (Nat.cast_nonneg (k*(k-j))) hc hscale hm
  constructor
  · convert hh.1 using 1 <;> ring
  · exact hh.2

#print axioms source_minor_normalized_bounds
end Waring.PolicyCompletionMinorRanges
