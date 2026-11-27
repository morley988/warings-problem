import Waring.FirstDifferenceBox
import Waring.CoefficientPower

/-!
# The literal first-difference source second moment in degrees8,16,18

The source height range, smooth coefficient block M<m<=MR and center range
1<=z<=2P are retained. The extra R factor in the cardinality is absorbed by
an explicit positive smoothness choice, after the genuine divisor-fiber L2
estimate has been proved.
-/

noncomputable section
open scoped BigOperators
namespace Waring.FirstDifferenceSecond
open IntegerDifferencePolynomial CoefficientPower SmoothMoments

theorem actual_first_difference_second_scaled (d : ℕ) (hd : supportedHalfDegree d)
    (L : ℝ) (hL : 1 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ A : Finset Index,
      (∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) →
      (∀ x ∈ A, (x.1 : ℝ) ≤ L*P ∧ (x.2.1 : ℝ) ≤ L*P ∧ (x.2.2 : ℝ) ≤ L*P) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ A, fourier
          ((powerPolynomial (2*d) [((x.1 : ℤ),(x.2.1 : ℤ))]).eval (x.2.2 : ℤ))
          (α : AddCircle (1 : ℝ))‖^2) ≤ C*P^ε*(A.card : ℝ) := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := actual_first_difference_second_on_box d hd hε
  refine ⟨C*L^ε,mul_pos hC (Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _),P₀,hP₀,?_⟩
  intro P hP A hpos hbox
  have hP0 : 0 ≤ P := zero_le_one.trans (hP₀.trans hP)
  have hPL : P₀ ≤ L*P := hP.trans (le_mul_of_one_le_left hP0 hL)
  convert hbound (L*P) hPL A hpos hbox using 1
  rw [Real.mul_rpow (zero_le_one.trans hL) hP0]
  ring

def sourceFirstDomain (P H Q R M : ℝ) : Finset Index :=
  Finset.Icc 1 ⌊H⌋₊ ×ˢ (coefficientBlock Q R M ×ˢ Finset.Icc 1 ⌊2*P⌋₊)

def sourceFirstSum (d : ℕ) (P H Q R M α : ℝ) : ℂ :=
  ∑ x ∈ sourceFirstDomain P H Q R M,
    fourier ((powerPolynomial (2*d) [((x.1 : ℤ),(x.2.1 : ℤ))]).eval (x.2.2 : ℤ))
      (α : AddCircle (1 : ℝ))

theorem sourceFirstDomain_card {P H Q R M : ℝ}
    (hP : 0 ≤ P) (hH : 0 ≤ H) (hMR : 0 ≤ M*R) :
    ((sourceFirstDomain P H Q R M).card : ℝ) ≤ 2*P*H*M*R := by
  have hc : ((coefficientBlock Q R M).card : ℝ) ≤ M*R := by
    calc
      _ ≤ ((smoothNumbers (M*R) R).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (coefficientBlock_subset Q R M)
      _ ≤ (⌊M*R⌋₊ : ℝ) := by exact_mod_cast smoothNumbers_card_le (M*R) R
      _ ≤ M*R := Nat.floor_le hMR
  simp only [sourceFirstDomain,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel,
    Nat.cast_mul]
  calc
    _ ≤ H*((M*R)*(2*P)) :=
      mul_le_mul (Nat.floor_le hH)
        (mul_le_mul hc (Nat.floor_le (by positivity : 0 ≤ 2*P))
          (Nat.cast_nonneg _) hMR) (by positivity) hH
    _ = _ := by ring

/-- The actual source estimate F1 L2 << P^(1+epsilon) M H in the three
even degrees, with an explicit smoothness exponent epsilon/2. -/
theorem source_first_second_moment (d : ℕ) (hd : supportedHalfDegree d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H Q R M : ℝ, 1 ≤ H → H ≤ 2*P → 1 ≤ M → 1 ≤ R →
      M*R ≤ 2*P → R ≤ P^(ε/2) →
      (∫ α in (0 : ℝ)..1, ‖sourceFirstSum d P H Q R M α‖^2) ≤
        C*P^(1+ε)*M*H := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := actual_first_difference_second_scaled d hd
    2 (by norm_num) (show 0 < ε/2 by positivity)
  refine ⟨2*C,by positivity,P₀,hP₀,?_⟩
  intro P hPP₀ H Q R M hH hHP hM hR hMR hRP
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hpos : ∀ x ∈ sourceFirstDomain P H Q R M,
      0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2 := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hh,hmz⟩
    rcases Finset.mem_product.mp hmz with ⟨hm,hz⟩
    have hm' := (mem_smoothNumbers.mp (Finset.mem_filter.mp hm).1).1.1
    exact ⟨(Finset.mem_Icc.mp hh).1,hm',(Finset.mem_Icc.mp hz).1⟩
  have hbox : ∀ x ∈ sourceFirstDomain P H Q R M,
      (x.1 : ℝ) ≤ 2*P ∧ (x.2.1 : ℝ) ≤ 2*P ∧ (x.2.2 : ℝ) ≤ 2*P := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hh,hmz⟩
    rcases Finset.mem_product.mp hmz with ⟨hm,hz⟩
    refine ⟨((Nat.cast_le.mpr (Finset.mem_Icc.mp hh).2).trans (Nat.floor_le hH0)).trans hHP,
      ((Finset.mem_filter.mp hm).2.2).trans hMR,?_⟩
    exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hz).2).trans (Nat.floor_le (by positivity))
  have hb := hbound P hPP₀ (sourceFirstDomain P H Q R M) hpos hbox
  change (∫ α in (0 : ℝ)..1, ‖sourceFirstSum d P H Q R M α‖^2) ≤ _ at hb
  calc
    _ ≤ C*P^(ε/2)*((sourceFirstDomain P H Q R M).card : ℝ) := hb
    _ ≤ C*P^(ε/2)*(2*P*H*M*R) :=
      mul_le_mul_of_nonneg_left (sourceFirstDomain_card hPpos.le hH0 (mul_nonneg hM0 hR0))
        (mul_nonneg hC.le (Real.rpow_nonneg hPpos.le _))
    _ ≤ C*P^(ε/2)*(2*P*H*M*P^(ε/2)) := by gcongr
    _ = (2*C)*P^(1+ε)*M*H := by
      rw [Real.rpow_add hPpos,Real.rpow_one,
        show ε = ε/2+ε/2 by ring,Real.rpow_add hPpos]
      ring

#print axioms actual_first_difference_second_scaled
#print axioms source_first_second_moment
end Waring.FirstDifferenceSecond
