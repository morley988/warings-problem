import Waring.FirstDifferenceCount

/-!
# Unconditional first-difference L2 bounds on the source parameter boxes

An explicit polynomial-size estimate discharges the frequency-size premise
in the divisor-fiber bound. The resulting moment is bounded by P^epsilon
times the actual number of height/coefficient/center labels.
-/

noncomputable section
open scoped BigOperators
namespace Waring.FirstDifferenceSecond
open IntegerDifferencePolynomial

def phaseCoefficient (d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range d, 2*(2*d).choose (2*i+1)

theorem evenPhase_real_le {d h m z : ℕ} (hd : 2 ≤ d) {P : ℝ} (hP : 1 ≤ P)
    (hh : (h : ℝ) ≤ P) (hm : (m : ℝ) ≤ P) (hz : (z : ℝ) ≤ P) :
    (evenPhase d h m z : ℝ) ≤ (phaseCoefficient d : ℝ)*P^((2*d)*(2*d-1)) := by
  unfold evenPhase phaseCoefficient
  rw [Nat.cast_sum,Nat.cast_sum,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hsub : 2*i+1+(2*d-(2*i+1))=2*d := by omega
  have he : 2*i+1+(2*d-(2*i+1))+(2*d)*(2*i) ≤ (2*d)*(2*d-1) := by
    rw [hsub]
    calc
      2*d+(2*d)*(2*i) = (2*d)*(2*i+1) := by ring
      _ ≤ (2*d)*(2*d-1) := Nat.mul_le_mul_left _ (by omega)
  push_cast
  calc
    _ ≤ 2*((2*d).choose (2*i+1) : ℝ)*P^(2*i+1)*P^(2*d-(2*i+1))*P^((2*d)*(2*i)) := by
      gcongr
    _ = (2*((2*d).choose (2*i+1) : ℝ))*P^(2*i+1+(2*d-(2*i+1))+(2*d)*(2*i)) := by
      rw [pow_add,pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP he) (by positivity)

theorem indexPhase_magnitude_on_box (d : ℕ) (hd : 2 ≤ d) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → ∀ x : Index,
      (x.1 : ℝ) ≤ P → (x.2.1 : ℝ) ≤ P → (x.2.2 : ℝ) ≤ P →
      ((indexPhase d x).natAbs : ℝ) ≤ P^(((2*d)*(2*d-1)+1 : ℕ) : ℝ) := by
  refine ⟨max 1 (phaseCoefficient d : ℝ),le_max_left _ _,?_⟩
  intro P hPP₀ x hh hm hz
  have hP : 1 ≤ P := (le_max_left _ _).trans hPP₀
  have hC : (phaseCoefficient d : ℝ) ≤ P := (le_max_right _ _).trans hPP₀
  simp only [indexPhase,Int.natAbs_natCast,Real.rpow_natCast]
  calc
    _ ≤ (phaseCoefficient d : ℝ)*P^((2*d)*(2*d-1)) := evenPhase_real_le hd hP hh hm hz
    _ ≤ P*P^((2*d)*(2*d-1)) :=
      mul_le_mul_of_nonneg_right hC (pow_nonneg (zero_le_one.trans hP) _)
    _ = _ := by rw [pow_succ]; ring

/-- No frequency or mean-value estimate is a premise: this is the actual
diagonal-sized second moment on any positive finite box in degree8/16/18. -/
theorem actual_first_difference_second_on_box (d : ℕ) (hd : supportedHalfDegree d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ A : Finset Index,
      (∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) →
      (∀ x ∈ A, (x.1 : ℝ) ≤ P ∧ (x.2.1 : ℝ) ≤ P ∧ (x.2.2 : ℝ) ≤ P) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ A, fourier
          ((powerPolynomial (2*d) [((x.1 : ℤ),(x.2.1 : ℤ))]).eval (x.2.2 : ℤ))
          (α : AddCircle (1 : ℝ))‖^2) ≤ C*P^ε*(A.card : ℝ) := by
  have hd2 : 2 ≤ d := by rcases hd with rfl | rfl | rfl <;> norm_num
  obtain ⟨C,hC,hbound⟩ := first_difference_second_moment
    (B := (((2*d)*(2*d-1)+1 : ℕ) : ℝ)) (by positivity) hε
  obtain ⟨P₀,hP₀,hsize⟩ := indexPhase_magnitude_on_box d hd2
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP₀ A hpos hbox
  have hsum (α : ℝ) :
      (∑ x ∈ A, fourier
        ((powerPolynomial (2*d) [((x.1 : ℤ),(x.2.1 : ℤ))]).eval (x.2.2 : ℤ))
        (α : AddCircle (1 : ℝ))) =
      ∑ x ∈ A, fourier (indexPhase d x) (α : AddCircle (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← evenPhase_eq_powerPolynomial hd x.1 x.2.1 x.2.2 (hpos x hx).2.1]
    rfl
  simp_rw [hsum]
  exact hbound P (hP₀.trans hPP₀) d hd2 A
    (fun x hx => ⟨(hpos x hx).1,(hpos x hx).2.2⟩)
    (fun x hx => hsize P hPP₀ x (hbox x hx).1 (hbox x hx).2.1 (hbox x hx).2.2)

#print axioms indexPhase_magnitude_on_box
#print axioms actual_first_difference_second_on_box
end Waring.FirstDifferenceSecond
