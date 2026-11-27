import Waring.PolicyCompletionSmallSmooth

/-!
# Uniform shorter-cutoff smooth moments

This proves the actual content of Brudern--Wooley2023 Lemma2.1 from the
definition of a genuinely admissible exponent. A single positive smoothness
choice works simultaneously for every real length1<=Y<=P, even when Y is
too small for its own asymptotic threshold or for R<=Y^eta.
-/

noncomputable section
namespace Waring.SmoothMoments

theorem admissibleExponent_uniform_shorter {k p : ℕ} {lam : ℝ}
    (hadm : AdmissibleExponent k p lam) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
      ∀ P : ℝ, 1 ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ Y : ℝ, 1 ≤ Y → Y ≤ P →
        smoothMoment k p Y R ≤ C*P^ε*Y^lam := by
  have hlam : 0 ≤ lam := admissibleExponent_nonneg hadm
  obtain ⟨η₁,hη₁,C₁,hC₁,Y₀,hY₀,hbound⟩ := hadm ε hε
  let ν : ℝ := ε/((p : ℝ)+1)
  have hν : 0 < ν := div_pos hε (by positivity)
  have hνp : ν*(p : ℝ) ≤ ε := by
    have hid : ν*((p : ℝ)+1)=ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  let C : ℝ := max 1 (max C₁ (Y₀^p))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC₁C : C₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hY₀C : Y₀^p ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨ν*η₁,mul_pos hν hη₁,C,zero_lt_one.trans_le hC1,?_⟩
  intro P hP R hR hRP Y hY hYP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hPε : 1 ≤ P^ε := Real.one_le_rpow hP hε.le
  have hYlam : 1 ≤ Y^lam := Real.one_le_rpow hY hlam
  have hCbound : C ≤ C*P^ε*Y^lam := by
    calc
      C ≤ C*P^ε := le_mul_of_one_le_right (zero_le_one.trans hC1) hPε
      _ ≤ C*P^ε*Y^lam := le_mul_of_one_le_right (by positivity) hYlam
  by_cases hYY₀ : Y ≤ Y₀
  · exact ((smoothMoment_le_trivial k p R hYp.le).trans
      (pow_le_pow_left₀ hYp.le hYY₀ p)).trans (hY₀C.trans hCbound)
  by_cases hYsmall : Y ≤ P^ν
  · have hsmall : smoothMoment k p Y R ≤ P^ε := by
      calc
        _ ≤ Y^p := smoothMoment_le_trivial k p R hYp.le
        _ ≤ (P^ν)^p := pow_le_pow_left₀ hYp.le hYsmall p
        _ = P^(ν*(p : ℝ)) := (Real.rpow_mul_natCast hPp.le _ _).symm
        _ ≤ P^ε := Real.rpow_le_rpow_of_exponent_le hP hνp
    apply hsmall.trans
    calc
      P^ε ≤ C*P^ε := le_mul_of_one_le_left (Real.rpow_nonneg hPp.le _) hC1
      _ ≤ C*P^ε*Y^lam := le_mul_of_one_le_right (by positivity) hYlam
  · have hRY : R ≤ Y^η₁ := by
      calc
        R ≤ P^(ν*η₁) := hRP
        _ = (P^ν)^η₁ := Real.rpow_mul hPp.le _ _
        _ ≤ Y^η₁ := Real.rpow_le_rpow (Real.rpow_nonneg hPp.le _)
          (le_of_not_ge hYsmall) hη₁.le
    calc
      _ ≤ C₁*Y^(lam+ε) := hbound Y (le_of_not_ge hYY₀) R hR hRY
      _ = C₁*Y^lam*Y^ε := by rw [Real.rpow_add hYp]; ring
      _ ≤ C*Y^lam*P^ε :=
        mul_le_mul (mul_le_mul_of_nonneg_right hC₁C (Real.rpow_nonneg hYp.le _))
          (Real.rpow_le_rpow hYp.le hYP hε.le) (Real.rpow_nonneg hYp.le _)
          (by positivity)
      _ = C*P^ε*Y^lam := by ring

#print axioms admissibleExponent_uniform_shorter
end Waring.SmoothMoments
