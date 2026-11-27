import Waring.SeedCompletionEvenDoubleIdentity
import Waring.SeedCompletionEvenDoubleCount
import Waring.SeedCompletionPhaseSize

/-! # Actual even j=2 second moment on positive Cartesian boxes -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEvenDoubleBox
open SeedCompletionEvenDouble SeedCompletionEvenDoubleCount
  IntegerDifferencePolynomial FirstDifferenceSecond

def actualSum (d : ℕ) (H B : Finset Pair) (Z : Finset ℕ) (α : ℝ) : ℂ :=
  ∑ x ∈ H ×ˢ (B ×ˢ Z),fourier
    ((powerPolynomial (2*d) [((x.1.2 : ℤ),(x.2.1.2 : ℤ)),
      ((x.1.1 : ℤ),(x.2.1.1 : ℤ))]).eval (x.2.2 : ℤ)) (α : AddCircle (1 : ℝ))

theorem actual_second_on_box (d : ℕ) (hd : supportedHalfDegree d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      ∀ (H B : Finset Pair) (Z : Finset ℕ),
      (∀ h ∈ H,0 < h.1 ∧ 0 < h.2 ∧ (h.1 : ℝ) ≤ P ∧ (h.2 : ℝ) ≤ P) →
      (∀ m ∈ B,0 < m.1 ∧ 0 < m.2 ∧ (m.1 : ℝ) ≤ P ∧ (m.2 : ℝ) ≤ P) →
      (∀ z ∈ Z,0 < z ∧ (z : ℝ) ≤ P) →
      (B.card : ℝ) ≤ P^(1/3 : ℝ) → (Z.card : ℝ) ≤ P →
      (∫ α in (0 : ℝ)..1,‖actualSum d H B Z α‖^2) ≤
        C*P^(1+ε)*(H.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨P₀,hP₀,hsize⟩ := powerPolynomial_magnitude_polynomial_bound (2*d) 2
  obtain ⟨C,hC,hbound⟩ := second_moment d hd
    (L := (((2*d+1)*(2*d)+1 : ℕ) : ℝ)) (by positivity) hε
  have hK : 0 ≤ curveConstant d := by unfold curveConstant; positivity
  refine ⟨C*(2+curveConstant d),by positivity,P₀,hP₀,?_⟩
  intro P hPP₀ H B Z hH hB hZ hBc hZc
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hs : ∀ x ∈ H ×ˢ (B ×ˢ Z),((indexPhase d x).natAbs : ℝ) ≤
      P^(((2*d+1)*(2*d)+1 : ℕ) : ℝ) := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hh,hmz⟩
    rcases Finset.mem_product.mp hmz with ⟨hm,hz⟩
    change ((phase d x.1 x.2.1 x.2.2 : ℤ).natAbs : ℝ) ≤ _
    rw [phase_eq_powerPolynomial hd _ _ _ (hB _ hm).1 (hB _ hm).2.1]
    apply hsize P hPP₀ _ (by simp)
    · intro p hp
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl
      · change (x.2.1.2 : ℤ) ≠ 0
        exact_mod_cast (hB _ hm).2.1.ne'
      · change (x.2.1.1 : ℤ) ≠ 0
        exact_mod_cast (hB _ hm).1.ne'
    · intro p hp
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl
      · simpa using And.intro (hH _ hh).2.2.2 (hB _ hm).2.2.2
      · simpa using And.intro (hH _ hh).2.2.1 (hB _ hm).2.2.1
    · simpa using (hZ _ hz).2
  have hb := hbound P hP H B Z
    (fun h hh => ⟨(hH h hh).1,(hH h hh).2.1⟩) hZ hs
  have hcurve : (B.card : ℝ)*P^(2/3 : ℝ) ≤ P := by
    calc
      _ ≤ P^(1/3 : ℝ)*P^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right hBc (by positivity)
      _ = P := by rw [← Real.rpow_add hPpos]; norm_num
  have hc : 2*(Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ)) ≤
      (2+curveConstant d)*P := by
    have hmul := mul_le_mul_of_nonneg_left hcurve hK
    nlinarith
  have heq (α : ℝ) : actualSum d H B Z α =
      ∑ x ∈ H ×ˢ (B ×ˢ Z),fourier (indexPhase d x) (α : AddCircle (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hm := (Finset.mem_product.mp (Finset.mem_product.mp hx).2).1
    rw [← phase_eq_powerPolynomial hd _ _ _ (hB _ hm).1 (hB _ hm).2.1]
    rfl
  simp_rw [heq]
  calc
    _ ≤ _ := hb
    _ ≤ C*P^ε*(H.card : ℝ)*(B.card : ℝ)*((2+curveConstant d)*P) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [Real.rpow_add hPpos,Real.rpow_one]; ring

/-- Fixed source dilations affect only the constant, while the original
coefficient-volume condition remains at the original ambient scale. -/
theorem actual_second_diagonal_size (d : ℕ) (hd : supportedHalfDegree d)
    (L : ℝ) (hL : 1 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      ∀ (H B : Finset Pair) (Z : Finset ℕ),
      (∀ h ∈ H,0 < h.1 ∧ 0 < h.2) →
      (∀ m ∈ B,0 < m.1 ∧ 0 < m.2) →
      (∀ z ∈ Z,0 < z) →
      (∀ h ∈ H,(h.1 : ℝ) ≤ L*P ∧ (h.2 : ℝ) ≤ L*P) →
      (∀ m ∈ B,(m.1 : ℝ) ≤ L*P ∧ (m.2 : ℝ) ≤ L*P) →
      (∀ z ∈ Z,(z : ℝ) ≤ L*P) →
      (B.card : ℝ) ≤ P^(1/3 : ℝ) → (Z.card : ℝ) ≤ L*P →
      (∫ α in (0 : ℝ)..1,‖actualSum d H B Z α‖^2) ≤
        C*P^(1+ε)*(H.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := actual_second_on_box d hd hε
  refine ⟨C*L^(1+ε),by positivity,P₀,hP₀,?_⟩
  intro P hPP H B Z hHp hBp hZp hHb hBb hZb hBc hZc
  have hP : 1 ≤ P := hP₀.trans hPP
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hPL : P ≤ L*P := le_mul_of_one_le_left hP0 hL
  have hb := hbound (L*P) (hPP.trans hPL) H B Z
    (fun h hh => ⟨(hHp h hh).1,(hHp h hh).2,hHb h hh⟩)
    (fun m hm => ⟨(hBp m hm).1,(hBp m hm).2,hBb m hm⟩)
    (fun z hz => ⟨hZp z hz,hZb z hz⟩)
    (hBc.trans (Real.rpow_le_rpow hP0 hPL (by norm_num))) hZc
  exact hb.trans_eq (by rw [Real.mul_rpow (zero_le_one.trans hL) hP0]; ring)

#print axioms actual_second_on_box
#print axioms actual_second_diagonal_size
end Waring.SeedCompletionEvenDoubleBox
