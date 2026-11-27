import Waring.RestrictedSmoothScaledMoments

/-! # Finite denominator sums of the literal arc integrals -/

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Waring.RestrictedSmoothArcs

theorem rationalArcSum_nonneg (q : ℕ) [NeZero q] {δ : ℝ} (hδ : 0 ≤ δ)
    {F : ℝ → ℝ} (hF : ∀ x,0 ≤ F x) : 0 ≤ rationalArcSum q F δ := by
  unfold rationalArcSum
  apply Finset.sum_nonneg
  intro a ha
  exact intervalIntegral.integral_nonneg_of_forall
    (by have := div_nonneg hδ (Nat.cast_nonneg q); linarith) (fun x => hF _)

theorem rationalArcSum_mono (q : ℕ) [NeZero q] {δ : ℝ} (hδ : 0 ≤ δ)
    {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) (hFG : ∀ x,F x ≤ G x) :
    rationalArcSum q F δ ≤ rationalArcSum q G δ := by
  unfold rationalArcSum
  apply Finset.sum_le_sum
  intro a ha
  apply intervalIntegral.integral_mono_on
    (by have := div_nonneg hδ (Nat.cast_nonneg q); linarith)
    ((hF.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
    ((hG.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
  exact fun x _ => hFG _

theorem rationalArcSum_const_mul (q : ℕ) [NeZero q] (F : ℝ → ℝ) (δ C : ℝ) :
    rationalArcSum q (fun x => C*F x) δ=C*rationalArcSum q F δ := by
  unfold rationalArcSum
  simp_rw [intervalIntegral.integral_const_mul]
  exact (Finset.mul_sum _ _ _).symm

theorem rationalArcSum_finset_sum {ι : Type*} (A : Finset ι)
    (q : ℕ) [NeZero q] (F : ι → ℝ → ℝ) (δ : ℝ) (hF : ∀ i ∈ A,Continuous (F i)) :
    rationalArcSum q (fun x => ∑ i ∈ A,F i x) δ = ∑ i ∈ A,rationalArcSum q (F i) δ := by
  unfold rationalArcSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  exact intervalIntegral.integral_finset_sum
    (fun i hi => ((hF i hi).comp (continuous_const.add continuous_id)).intervalIntegrable _ _)

theorem rationalArcSum_constant_le (q : ℕ) [NeZero q] {δ C : ℝ}
    (hδ : 0 ≤ δ) (hC : 0 ≤ C) : rationalArcSum q (fun _ => C) δ ≤ 2*δ*C := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hc : Fintype.card (ZMod q)ˣ ≤ q := by
    have h := Fintype.card_le_of_injective (fun u : (ZMod q)ˣ => (u : ZMod q)) Units.val_injective
    simpa only [ZMod.card] using h
  have hint : (∫ x in -(δ/(q : ℝ))..δ/(q : ℝ), C) = 2*δ/(q : ℝ)*C := by
    rw [intervalIntegral.integral_const,smul_eq_mul]
    ring
  unfold rationalArcSum
  simp only [hint,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  calc
    _ ≤ (q : ℝ)*(2*δ/(q : ℝ)*C) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (by positivity)
    _ = _ := by field_simp

def denominatorArcLabels (S : Finset ℕ+) : Finset ArcLabel :=
  S.sigma (fun _ => Finset.univ)

theorem sum_rationalArcSum_le (S : Finset ℕ+) {Q δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*Q*δ ≤ 1)
    (hQ : ∀ q ∈ S,(q : ℝ) ≤ Q)
    {F : ℝ → ℝ} (hF : Continuous F) (hper : Function.Periodic F 1)
    (hF0 : ∀ x,0 ≤ F x) :
    (∑ q ∈ S,rationalArcSum (q : ℕ) F δ) ≤ 3*∫ x in (0 : ℝ)..1,F x := by
  have h := sum_arcLabelIntegral_le (denominatorArcLabels S) hδ hδ1 hsmall
    (fun p hp => hQ p.1 (Finset.mem_sigma.mp hp).1) hF hper hF0
  simpa only [denominatorArcLabels,Finset.sum_sigma,arcLabelIntegral,rationalArcSum] using h

theorem denominator_card_le (S : Finset ℕ+) {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hQ : ∀ q ∈ S,(q : ℝ) ≤ Q) : (S.card : ℝ) ≤ Q := by
  have hc : S.card ≤ (Finset.Icc 1 ⌊Q⌋₊).card := Finset.card_le_card_of_injOn
    (fun q : ℕ+ => (q : ℕ))
    (fun q hq => Finset.mem_Icc.mpr ⟨q.pos,Nat.le_floor (hQ q hq)⟩)
    (fun _ _ _ _ he => Subtype.ext he)
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at hc
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hQ0)

theorem sum_constant_arc_integrals_le (S : Finset ℕ+) {Q δ C : ℝ}
    (hQ0 : 0 ≤ Q) (hQ : ∀ q ∈ S,(q : ℝ) ≤ Q) (hδ : 0 ≤ δ) (hC : 0 ≤ C) :
    (∑ q ∈ S,rationalArcSum (q : ℕ) (fun _ => C) δ) ≤ 2*Q*δ*C := by
  calc
    _ ≤ ∑ q ∈ S,2*δ*C := Finset.sum_le_sum (fun q _ => rationalArcSum_constant_le q hδ hC)
    _ = (S.card : ℝ)*(2*δ*C) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ Q*(2*δ*C) := mul_le_mul_of_nonneg_right (denominator_card_le S hQ0 hQ) (by positivity)
    _ = _ := by ring

#print axioms sum_rationalArcSum_le
#print axioms sum_constant_arc_integrals_le
end Waring.RestrictedSmoothArcs
