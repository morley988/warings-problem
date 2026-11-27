import Waring.ProductMultiplicity
import Waring.EvenMoments
import Mathlib.Algebra.BigOperators.Associated

/-! # An elementary almost-linear supply of smooth integers

Products of L integers in [1,M] are M-smooth and at most M^L. The actual
divisor multiplicity bound turns their M^L labelled products into a
uniform lower bound for the number of distinct smooth integers.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SmoothMoments
open ProductMultiplicity

theorem product_box_mem_smooth (L M : ℕ) (hM : 1 ≤ M) {x : Fin L → ℕ}
    (hx : x ∈ finiteTuples (Finset.Icc 1 M) L) :
    tupleProduct x ∈ smoothNumbers ((M : ℝ)^L) M := by
  have hxi : ∀ i : Fin L,1 ≤ x i ∧ x i ≤ M := by
    intro i
    exact Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hx) i)
  have hpositive : 0 < tupleProduct x := Finset.prod_pos (fun i _ => (hxi i).1)
  have hbound : tupleProduct x ≤ M^L := by
    calc
      _ ≤ ∏ _i : Fin L,M := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => (hxi i).2)
      _ = _ := by simp
  apply mem_smoothNumbers.mpr
  refine ⟨⟨hpositive,?_⟩,?_⟩
  · simpa only [← Nat.cast_pow,Nat.floor_natCast] using hbound
  · intro q hq hdiv
    obtain ⟨i,_,hi⟩ := (hq.prime.dvd_finset_prod_iff x).mp hdiv
    exact_mod_cast (Nat.le_of_dvd ((hxi i).1) hi).trans (hxi i).2

theorem product_box_card_bound (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ M : ℕ,1 ≤ M →
      (M : ℝ)^L ≤ C*((M : ℝ)^L)^ε*
        ((smoothNumbers ((M : ℝ)^L) M).card : ℝ) := by
  obtain ⟨C,hC,hfiber⟩ := productFiber_card_le_rpow L hε
  refine ⟨C,hC,?_⟩
  intro M hM
  let A := finiteTuples (Finset.Icc 1 M) L
  let B := smoothNumbers ((M : ℝ)^L) M
  have hcard : A.card=M^L := by simp [A,finiteTuples,Fintype.card_piFinset]
  have hmap : Set.MapsTo tupleProduct A B := fun x hx => product_box_mem_smooth L M hM hx
  have he : A.card=∑ n ∈ B,(productFiber A n).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  calc
    _ = (A.card : ℝ) := by rw [hcard,Nat.cast_pow]
    _ = ∑ n ∈ B,((productFiber A n).card : ℝ) := by exact_mod_cast he
    _ ≤ ∑ _n ∈ B,C*((M : ℝ)^L)^ε := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨⟨hn1,hnM⟩,_⟩ := mem_smoothNumbers.mp hn
      have hnp : (n : ℝ) ≤ (M : ℝ)^L :=
        (Nat.le_floor_iff (by positivity)).mp hnM
      exact (hfiber A n hn1).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnp hε.le) hC.le)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- This lower bound is along integer product scales P=M^L. Choosing
L*eta≥1 makes its smoothness cutoff M admissible at the scale P. -/
theorem smooth_card_lower_product_scale (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ,0 < c ∧ ∀ M : ℕ,1 ≤ M →
      c*((M : ℝ)^L)^(1-ε) ≤ ((smoothNumbers ((M : ℝ)^L) M).card : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := product_box_card_bound L hε
  refine ⟨C⁻¹,inv_pos.mpr hC,?_⟩
  intro M hM
  have hP : 0 < (M : ℝ)^L := by
    apply pow_pos
    exact_mod_cast (zero_lt_one.trans_le hM)
  apply (mul_le_mul_left (show 0 < C*((M : ℝ)^L)^ε by positivity)).mp
  calc
    _ = (C*C⁻¹)*(((M : ℝ)^L)^ε*((M : ℝ)^L)^(1-ε)) := by ring
    _ = (M : ℝ)^L := by
      rw [mul_inv_cancel₀ hC.ne',one_mul,← Real.rpow_add hP,
        show ε+(1-ε)=1 by ring,Real.rpow_one]
    _ ≤ _ := hbound M hM

theorem product_scale_smoothness {η : ℝ} {L M : ℕ} (hM : 1 ≤ M)
    (hLη : 1 ≤ (L : ℝ)*η) : (M : ℝ) ≤ ((M : ℝ)^L)^η := by
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  calc
    (M : ℝ) = (M : ℝ)^(1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (M : ℝ)^((L : ℝ)*η) := Real.rpow_le_rpow_of_exponent_le hMreal hLη
    _ = _ := by rw [Real.rpow_mul (Nat.cast_nonneg _),Real.rpow_natCast]

#print axioms smooth_card_lower_product_scale
#print axioms product_scale_smoothness
end Waring.SmoothMoments
