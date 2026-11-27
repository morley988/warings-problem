import Waring.PolicyCompletionResourceActual
import Waring.PolicyCompletionSourceCartesian

/-! # Actual box cardinality and coefficient support at the source scale -/
noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionParameterScale
open PolicyCompletionResourceActual PolicyCompletionMajorPowerRanges PolicyCompletionScaledBounds
open CartesianMomentAdapters CartesianProductSampling ProductMultiplicity ResourceDifferencingCap
open SmoothMoments

theorem realBox_nonempty_of_pos {j : ℕ} (bounds : Fin j→ℕ) (hb : ∀i,0<bounds i) :
    (realBox bounds).Nonempty := by
  apply Finset.Nonempty.image
  refine ⟨fun _=>1,mem_positiveBox.mpr (fun i=>⟨le_rfl,hb i⟩)⟩

theorem coefficientCaps_pos {j : ℕ} {P R : ℝ} (hP : 0<P) (hR : 0<R)
    (φ : Fin j→ℝ) (i : Fin j) : 0<coefficientCaps φ P R i :=
  mul_pos (Real.rpow_pos_of_pos hP _) hR

theorem coefficientSets_real_card {j : ℕ} {P R : ℝ} (hP : 0≤P) (hR : 0≤R)
    (φ : Fin j→ℝ) (i : Fin j) :
    (((realCoefficientSets (coefficientSets φ P R) i).card):ℝ)≤coefficientCaps φ P R i := by
  calc
    _ ≤ ((coefficientSets φ P R i).card:ℝ) := by
      exact_mod_cast Finset.card_image_le
    _ ≤ ((smoothNumbers (P^(φ i)*R) R).card:ℝ) := by
      exact_mod_cast Finset.card_le_card (CoefficientPower.coefficientBlock_subset P R (P^(φ i)))
    _ ≤ (⌊P^(φ i)*R⌋₊:ℝ) := by exact_mod_cast smoothNumbers_card_le (P^(φ i)*R) R
    _ ≤ _ := Nat.floor_le (mul_nonneg (Real.rpow_nonneg hP _) hR)

theorem coefficientSets_real_ne_zero {j : ℕ} (P R : ℝ) (φ : Fin j→ℝ) :
    ∀i,∀m∈realCoefficientSets (coefficientSets φ P R) i,m≠0 := by
  intro i m hm
  rcases Finset.mem_image.mp hm with ⟨n,hn,rfl⟩
  have hp := (mem_smoothNumbers.mp (Finset.mem_filter.mp hn).1).1.1
  exact_mod_cast (show n≠0 by omega)

theorem realBox_card_power {j : ℕ} {D P : ℝ} (hD : 0≤D) (hP : 0≤P)
    (e : Fin j→ℝ) (he : ∀i,0≤e i) :
    ((realBox (scaledBounds D P e)).card:ℝ)≤D^j*P^(∑i,e i) := by
  rw [realBox_card,tupleProduct,Nat.cast_prod]
  calc
    _ ≤ ∏i,D*P^(e i) := Finset.prod_le_prod (fun _ _=>Nat.cast_nonneg _)
      (fun i _=>Nat.floor_le (mul_nonneg hD (Real.rpow_nonneg hP _)))
    _ = _ := scaled_power_product e he hP

theorem coefficientCaps_product {j : ℕ} {P R : ℝ} (hP : 0<P)
    (φ : Fin j→ℝ) (hφ : ∀i,0≤φ i) :
    (∏i,coefficientCaps φ P R i)=P^(total φ)*R^j := by
  simp only [coefficientCaps,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [power_parameters_product hP φ hφ]

theorem source_parameter_scale {j : ℕ} (k : ℕ) {D P R : ℝ}
    (hD : 0≤D) (hP : 0<P) (hR : 0≤R) (φ : Fin j→ℝ)
    (hφ : ∀i,0≤φ i) (he : ∀i,0≤shiftExponents k φ i) :
    (⌊D*P⌋₊:ℝ)*parameterScale (realBox (scaledBounds D P (shiftExponents k φ)))
      (coefficientCaps φ P R)≤D^(j+1)*R^j*P^(amplitude k φ) := by
  have hH := realBox_card_power hD hP.le (shiftExponents k φ) he
  rw [shiftExponents_sum] at hH
  have hN := Nat.floor_le (mul_nonneg hD hP.le)
  unfold parameterScale
  rw [coefficientCaps_product hP φ hφ]
  calc
    _ ≤ (D*P)*((D^j*P^((j:ℝ)-(k:ℝ)*total φ))*(P^(total φ)*R^j)) := by
      gcongr
    _ = D^(j+1)*R^j*(P*P^((j:ℝ)-(k:ℝ)*total φ)*P^(total φ)) := by rw [pow_succ]; ring
    _ = _ := by
      congr 1
      nth_rw 1 [← Real.rpow_one P]
      rw [← Real.rpow_add hP,← Real.rpow_add hP]
      congr 1
      unfold amplitude
      ring

#print axioms source_parameter_scale
end Waring.PolicyCompletionParameterScale
