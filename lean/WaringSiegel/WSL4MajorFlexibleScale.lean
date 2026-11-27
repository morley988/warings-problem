import WaringSiegel.WSL4MajorFlexibleLocalized

/-! # Power cutoffs and the exact translation-radius loss -/
noncomputable section
set_option maxHeartbeats 1000000
open NumberField NumberField.mixedEmbedding Module
open scoped NumberField
namespace WaringSiegel.WSL4
open WSL3
variable {K : Type*} [Field K] [NumberField K]

theorem rpow_volume_commutes (P : ℝ) (hP : 0≤P) (d : ℕ) (lam : ℝ) :
    (P^lam)^d=(P^d)^lam := by
  rw [← Real.rpow_mul_natCast hP,← Real.rpow_natCast_mul hP]
  congr 1
  ring

theorem rpow_translation_window (P : ℝ) (hP : 1≤P) (R : ℕ) (hR : 1≤R)
    (lam : ℝ) (hlam0 : 0≤lam) (hlam1 : lam≤1) :
    1≤P^lam ∧ P^lam≤P ∧ (P^lam)^2≤P^(R+2)/P^lam ∧ P^(R+1)≤P^(R+2)/P^lam := by
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  have hB0 : 0<P^lam := Real.rpow_pos_of_pos hP0 lam
  have hB : P^lam≤P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hlam1
  refine ⟨Real.one_le_rpow hP hlam0,hB,?_,?_⟩
  · apply (le_div_iff₀ hB0).mpr
    calc
      (P^lam)^2*P^lam = (P^lam)^3 := by ring
      _ ≤ P^3 := pow_le_pow_left₀ hB0.le hB _
      _ ≤ P^(R+2) := pow_le_pow_right₀ hP (by omega)
  · apply (le_div_iff₀ hB0).mpr
    calc
      P^(R+1)*P^lam≤P^(R+1)*P := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = P^(R+2) := by rw [← pow_succ]

def shrinkingMinorArcs (k : ℕ) (lam P : ℝ) : Set (ArchimedeanTraceTorus K) :=
  (traceMajorArcUnion (P^k) ((k:ℝ)^finrank ℚ K * (P^finrank ℚ K)^lam))ᶜ

theorem shrinkingMinorArcs_eq_flexible (k : ℕ) (lam P : ℝ) (hP : 0<P) :
    shrinkingMinorArcs (K := K) k lam P =
      flexibleMinorArcs k (P^lam) (P^k/P^lam) := by
  unfold shrinkingMinorArcs flexibleMinorArcs
  rw [rpow_volume_commutes P hP.le]
  have he : P^lam*(P^k/P^lam)=P^k := by field_simp [(Real.rpow_pos_of_pos hP lam).ne']
  rw [he]

theorem shrinkingMinorArcs_measurable (k : ℕ) (lam P : ℝ) (hP : 0<P) :
    MeasurableSet (shrinkingMinorArcs (K := K) k lam P) :=
  (traceMajorArcUnion_measurableSet _ _ (pow_pos hP k)).compl

theorem flexible_volume_scale (P : ℝ) (hP : 0<P) (d a k : ℕ) (lam E : ℝ) :
    (P^d)^a*(P^k/P^lam)^d/(P^lam)^d*(P^d)^E =
      (P^d)^((a:ℝ)+k-2*lam+E) := by
  let X := P^d
  have hX : 0<X := pow_pos hP d
  have hPk : (P^k)^d=X^k := by dsimp [X]; rw [← pow_mul,← pow_mul,Nat.mul_comm k d]
  simp only [div_pow,rpow_volume_commutes P hP.le,hPk]
  change X^a*(X^k/X^lam)/X^lam*X^E=X^((a:ℝ)+k-2*lam+E)
  rw [← Real.rpow_natCast X a,← Real.rpow_natCast X k]
  calc
    _ = X^((a:ℝ)+(k:ℝ))/(X^(lam+lam))*X^E := by
      rw [Real.rpow_add hX,Real.rpow_add hX]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = X^(((a:ℝ)+(k:ℝ))-(lam+lam)+E) := by
      rw [← Real.rpow_sub hX,← Real.rpow_add hX]
    _ = _ := by congr 1; ring

#print axioms rpow_translation_window
#print axioms flexible_volume_scale
end WaringSiegel.WSL4
