import Waring.SeedCompletionEvenSecondCount
import Waring.SeedCompletionPhaseSize

/-! # The actual even second moment on boxes with a short coefficient range -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEvenSecondCount
open SeedCompletionEvenSecond IntegerDifferencePolynomial FirstDifferenceSecond

/-- The actual second-difference phase, retaining both positive heights and
all centers. Only the coefficient cardinality needs the P^(1/3) cap. -/
theorem actual_even_second_on_box (d : ℕ) (hd : supportedHalfDegree d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ (H : Finset (ℕ×ℕ)) (B Z : Finset ℕ),
      (∀ h ∈ H,0 < h.1 ∧ 0 < h.2 ∧ (h.1 : ℝ) ≤ P ∧ (h.2 : ℝ) ≤ P) →
      (∀ m ∈ B,0 < m ∧ (m : ℝ) ≤ P) →
      (∀ z ∈ Z,0 < z ∧ (z : ℝ) ≤ P) →
      (B.card : ℝ) ≤ P^(1/3 : ℝ) → (Z.card : ℝ) ≤ P →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ H ×ˢ (B ×ˢ Z),fourier
          ((powerPolynomial (2*d) [((x.1.2 : ℤ),1),((x.1.1 : ℤ),(x.2.1 : ℤ))]).eval
            (x.2.2 : ℤ)) (α : AddCircle (1 : ℝ))‖^2) ≤
        C*P^(1+ε)*(H.card : ℝ)*(B.card : ℝ) := by
  have hd2 : 2 ≤ d := by rcases hd with rfl | rfl | rfl <;> omega
  obtain ⟨P₀,hP₀,hsize⟩ := powerPolynomial_magnitude_polynomial_bound (2*d) 2
  obtain ⟨C,hC,hbound⟩ := second_moment d hd2
    (L := (((2*d+1)*(2*d)+1 : ℕ) : ℝ)) (by positivity) hε
  have hK : 0 ≤ curveConstant d := by unfold curveConstant; positivity
  refine ⟨C*(1+curveConstant d),by positivity,P₀,hP₀,?_⟩
  intro P hPP₀ H B Z hH hB hZ hBc hZc
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hs : ∀ x ∈ H ×ˢ (B ×ˢ Z),((indexPhase d x).natAbs : ℝ) ≤
      P^(((2*d+1)*(2*d)+1 : ℕ) : ℝ) := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hh,hmz⟩
    rcases Finset.mem_product.mp hmz with ⟨hm,hz⟩
    change ((phase d x.1.1 x.2.1 x.1.2 x.2.2 : ℤ).natAbs : ℝ) ≤ _
    rw [phase_eq_powerPolynomial hd _ _ _ _ (hB _ hm).1]
    apply hsize P hPP₀ _ (by simp)
    · intro p hp
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl
      · norm_num
      · change (x.2.1 : ℤ) ≠ 0
        exact_mod_cast (hB _ hm).1.ne'
    · intro p hp
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl
      · simpa using And.intro (hH _ hh).2.2.2 hP
      · simpa using And.intro (hH _ hh).2.2.1 (hB _ hm).2
    · simpa using (hZ _ hz).2
  have hb := hbound P hP H B Z
    (fun h hh => ⟨(hH h hh).1,(hH h hh).2.1⟩) hZ hs
  have hcurve : (B.card : ℝ)*P^(2/3 : ℝ) ≤ P := by
    calc
      _ ≤ P^(1/3 : ℝ)*P^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right hBc (by positivity)
      _ = P := by rw [← Real.rpow_add hPpos]; norm_num
  have hc : (Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ)) ≤
      (1+curveConstant d)*P := by
    have hmul := mul_le_mul_of_nonneg_left hcurve hK
    nlinarith
  have heq (α : ℝ) :
      (∑ x ∈ H ×ˢ (B ×ˢ Z),fourier
        ((powerPolynomial (2*d) [((x.1.2 : ℤ),1),((x.1.1 : ℤ),(x.2.1 : ℤ))]).eval
          (x.2.2 : ℤ)) (α : AddCircle (1 : ℝ))) =
      ∑ x ∈ H ×ˢ (B ×ˢ Z),fourier (indexPhase d x) (α : AddCircle (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hm := (Finset.mem_product.mp (Finset.mem_product.mp hx).2).1
    rw [← phase_eq_powerPolynomial hd _ _ _ _ (hB _ hm).1]
    rfl
  simp_rw [heq]
  calc
    _ ≤ _ := hb
    _ ≤ C*P^ε*(H.card : ℝ)*(B.card : ℝ)*((1+curveConstant d)*P) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [Real.rpow_add hPpos,Real.rpow_one]; ring

#print axioms actual_even_second_on_box
end Waring.SeedCompletionEvenSecondCount
