import Waring.SeedCompletionInitialMixed
import Waring.SeedCompletionSourceRecurrence

/-!
# The second efficient-differencing step on its literal first-source box

All height, coefficient, center and derivative conditions are discharged.
Only the actual next cross integral remains for the proved second-stage
terminal moment bounds.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionFirstMixedRecurrence
open SmoothMoments PolicyCompletionFundamental PolicyCompletionGoodBranch
open SeedCompletionInitialMixed SeedCompletionSourceRecurrence SeedCompletionSharpBackward

theorem first_labels_card_le {H Q R M : ℝ} (hH : 0 ≤ H) (hMR : 0 ≤ M*R) :
    ((firstLabels H Q R M).card : ℝ) ≤ H*M*R := by
  simp only [firstLabels,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_mul]
  calc
    _ ≤ H*(M*R) := mul_le_mul (Nat.floor_le hH)
      (FirstStageTransport.coefficientBlock_card_le hMR) (by positivity) hH
    _ = _ := by ring

theorem first_centers_card_le {P : ℝ} (hP : 0 ≤ P) :
    ((firstCenters P).card : ℝ) ≤ 2*P := by
  calc
    _ ≤ ((Finset.Icc 1 ⌊2*P⌋₊).card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    _ = (⌊2*P⌋₊ : ℝ) := by simp
    _ ≤ _ := Nat.floor_le (by positivity)

theorem first_centers_subset (P : ℝ) :
    firstCenters P ⊆ Finset.Icc 1 (⌊2*P⌋₊ : ℤ) := by
  intro z hz
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
  rcases Finset.mem_Icc.mp hn with ⟨hn1,hnP⟩
  apply Finset.mem_Icc.mpr
  exact ⟨by exact_mod_cast hn1,by exact_mod_cast hnP⟩

theorem first_mixed_recurrence (k s : ℕ) (hk : 2 ≤ k)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      ∀ H Qc Q R M₁ M₂ : ℝ,
      1 ≤ H → H ≤ 2*P → 1 ≤ M₁ → M₁*R ≤ 2*P →
      1 ≤ M₂ → M₂ ≤ Q → Q ≤ 4*P → (4*P)^η ≤ R →
      sourceMixedMoment k (s+1) (firstLabels H Qc R M₁) firstParameters (firstCenters P) Q R ≤
        K*P^ε*(H*M₁*R)*(M₂*R)^(2*(s+1)-1)*
          ((H*M₁*R)*(M₂*R)*(2*P)*smoothMoment k (2*(s+1)) (Q/M₂) R+
            nextSmoothCrossIntegral k (s+1) (firstLabels H Qc R M₁) firstParameters
              (CoefficientPower.coefficientBlock Q R M₂) (⌊2*P⌋₊ : ℤ) (Q/M₂) R) := by
  obtain ⟨K,hK,P₀,hP₀,hrec⟩ := source_recurrence (κ := ℕ × ℕ) k s hη hε
  refine ⟨K*4^ε,by positivity,P₀,hP₀,?_⟩
  intro P hPP H Qc Q R M₁ M₂ hH hHP hM₁ hM₁R hM₂ hM₂Q hQ hR
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have h4P : 1 ≤ 4*P := by linarith
  have hR1 : 1 ≤ R := (Real.one_le_rpow h4P hη.le).trans hR
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have hM₁0 : 0 ≤ M₁ := zero_le_one.trans hM₁
  have hM₂0 : 0 ≤ M₂ := zero_le_one.trans hM₂
  have hpos : ∀ c ∈ firstLabels H Qc R M₁,
      ∀ hm ∈ firstParameters c,0 < hm.1 ∧ 0 < hm.2 := by
    intro c hc p hp
    simp only [firstParameters,List.mem_singleton] at hp
    subst p
    obtain ⟨hh,hm⟩ := Finset.mem_product.mp hc
    have hhpos := (Finset.mem_Icc.mp hh).1
    have hmpos := (mem_smoothNumbers.mp (Finset.mem_filter.mp hm).1).1.1
    change (0 : ℤ) < (c.1 : ℤ) ∧ (0 : ℤ) < (c.2 : ℤ)
    exact ⟨by exact_mod_cast (show 0 < c.1 by omega),
      by exact_mod_cast (show 0 < c.2 by omega)⟩
  have hlen : ∀ c ∈ firstLabels H Qc R M₁,(firstParameters c).length < k := by
    intro c hc
    simpa only [firstParameters,List.length_singleton] using hk
  have hbox : ∀ c ∈ firstLabels H Qc R M₁,
      ∀ hm ∈ firstParameters c,(hm.1 : ℝ) ≤ 4*P ∧ (hm.2 : ℝ) ≤ 4*P := by
    intro c hc p hp
    simp only [firstParameters,List.mem_singleton] at hp
    subst p
    obtain ⟨hh,hm⟩ := Finset.mem_product.mp hc
    have hhH : (c.1 : ℝ) ≤ H :=
      (by exact_mod_cast (Finset.mem_Icc.mp hh).2 : (c.1 : ℝ) ≤ ⌊H⌋₊).trans
        (Nat.floor_le (zero_le_one.trans hH))
    have hmM : (c.2 : ℝ) ≤ M₁*R := (Finset.mem_filter.mp hm).2.2
    push_cast
    exact ⟨(hhH.trans hHP).trans (by linarith),(hmM.trans hM₁R).trans (by linarith)⟩
  have hNP : ((⌊2*P⌋₊ : ℤ) : ℝ) ≤ 4*P := by
    simp only [Int.cast_natCast]
    exact (Nat.floor_le (by positivity : 0 ≤ 2*P)).trans (by linarith)
  have hf := hrec (4*P) (hPP.trans (by linarith))
    (firstLabels H Qc R M₁) firstParameters hpos hlen hbox
    (⌊2*P⌋₊ : ℤ) hNP (firstCenters P) (first_centers_subset P)
    Q R M₂ hM₂ hM₂Q hQ hR
  have hC := first_labels_card_le (Q := Qc) (zero_le_one.trans hH) (mul_nonneg hM₁0 hR0)
  have hZ := first_centers_card_le hPp.le
  have hU := smoothMoment_nonneg k (2*(s+1)) (Q/M₂) R
  have hX := nextSmoothCrossIntegral_nonneg k (s+1) (firstLabels H Qc R M₁) firstParameters
    (CoefficientPower.coefficientBlock Q R M₂) (⌊2*P⌋₊ : ℤ) (Q/M₂) R
  apply hf.trans
  calc
    _ ≤ K*(4*P)^ε*(H*M₁*R)*(M₂*R)^(2*(s+1)-1)*
      ((H*M₁*R)*(M₂*R)*(2*P)*smoothMoment k (2*(s+1)) (Q/M₂) R+
        nextSmoothCrossIntegral k (s+1) (firstLabels H Qc R M₁) firstParameters
          (CoefficientPower.coefficientBlock Q R M₂) (⌊2*P⌋₊ : ℤ) (Q/M₂) R) := by
            gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hPp.le]; ring

#print axioms first_mixed_recurrence
end Waring.SeedCompletionFirstMixedRecurrence
