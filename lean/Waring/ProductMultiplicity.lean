import Waring.DivisorBound
import Mathlib.Data.Fintype.Pi

/-!
# Actual multiplicity of products of finitely many positive shifts

A fiber of the product of r natural coordinates injects into r-tuples of
divisors of the product. The proved divisor estimate therefore supplies the
usual arbitrarily small power loss. The weighted grouping theorem applies to
actual finite tuple families and nonnegative functions; no multiplicity bound
is left as an additional hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace Waring.ProductMultiplicity

def tupleProduct {r : ℕ} (x : Fin r → ℕ) : ℕ := ∏ i, x i

def productFiber {r : ℕ} (S : Finset (Fin r → ℕ)) (n : ℕ) : Finset (Fin r → ℕ) :=
  S.filter (fun x => tupleProduct x = n)

/-- Every coordinate in a positive-product fiber is a divisor of that product. -/
theorem productFiber_subset_divisor_tuples {r n : ℕ} (S : Finset (Fin r → ℕ))
    (hn : n ≠ 0) :
    productFiber S n ⊆ Fintype.piFinset (fun _ : Fin r => n.divisors) := by
  intro x hx
  have heq := (Finset.mem_filter.mp hx).2
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Nat.mem_divisors.mpr
  refine ⟨?_, hn⟩
  rw [← heq]
  exact Finset.dvd_prod_of_mem x (Finset.mem_univ i)

theorem productFiber_card_le_divisors {r n : ℕ} (S : Finset (Fin r → ℕ))
    (hn : n ≠ 0) : (productFiber S n).card ≤ n.divisors.card^r := by
  have h := Finset.card_le_card (productFiber_subset_divisor_tuples S hn)
  simpa only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using h

/-- One positive constant works for all finite families of r-tuples and every
positive product value. The rank r is fixed, while the families may vary. -/
theorem productFiber_card_le_rpow (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset (Fin r → ℕ), ∀ n : ℕ, 0 < n →
      ((productFiber S n).card : ℝ) ≤ C*(n : ℝ)^ε := by
  let δ : ℝ := ε/((r : ℝ)+1)
  have hr : (0 : ℝ) < (r : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hr
  have hδr : δ*(r : ℝ) ≤ ε := by
    have hid : δ*((r : ℝ)+1)=ε := div_mul_cancel₀ ε hr.ne'
    nlinarith
  obtain ⟨D,hD,hdiv⟩ := DivisorBound.divisor_count_le_rpow hδ
  refine ⟨D^r, by positivity, ?_⟩
  intro S n hn
  have hcard : ((productFiber S n).card : ℝ) ≤ (n.divisors.card : ℝ)^r := by
    exact_mod_cast productFiber_card_le_divisors S hn.ne'
  calc
    _ ≤ (n.divisors.card : ℝ)^r := hcard
    _ ≤ (D*(n : ℝ)^δ)^r := pow_le_pow_left₀ (by positivity) (hdiv n hn) r
    _ = D^r*(n : ℝ)^(δ*(r : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
    _ ≤ D^r*(n : ℝ)^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hδr) (by positivity)

/-- Exact regrouping by product, retaining the finite fiber multiplicity. -/
theorem sum_by_product {r : ℕ} (S : Finset (Fin r → ℕ)) (F : ℕ → ℝ) (H : ℕ)
    (hmap : ∀ x ∈ S, tupleProduct x ∈ Finset.Icc 1 H) :
    (∑ x ∈ S, F (tupleProduct x)) =
      ∑ n ∈ Finset.Icc 1 H, ((productFiber S n).card : ℝ)*F n := by
  rw [← Finset.sum_fiberwise_of_maps_to' hmap F]
  simp only [productFiber, Finset.sum_const, nsmul_eq_mul]

/-- Product grouping with a genuine H^epsilon factor, uniform over both the
finite tuple family and the nonnegative sampled quantity F. -/
theorem weighted_product_grouping_rpow (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 0 < H → ∀ S : Finset (Fin r → ℕ),
      ∀ F : ℕ → ℝ, (∀ x ∈ S, tupleProduct x ∈ Finset.Icc 1 H) →
      (∀ n ∈ Finset.Icc 1 H, 0 ≤ F n) →
      (∑ x ∈ S, F (tupleProduct x)) ≤ C*(H : ℝ)^ε*∑ n ∈ Finset.Icc 1 H, F n := by
  obtain ⟨C,hC,hfiber⟩ := productFiber_card_le_rpow r hε
  refine ⟨C,hC,?_⟩
  intro H _ S F hmap hF
  rw [sum_by_product S F H hmap, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hn1,hnH⟩
  have hnHR : (n : ℝ) ≤ (H : ℝ) := by exact_mod_cast hnH
  have hbound : ((productFiber S n).card : ℝ) ≤ C*(H : ℝ)^ε :=
    (hfiber S n (by omega)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hnHR hε.le) hC.le)
  exact mul_le_mul_of_nonneg_right hbound (hF n hn)

/-- The usual P^epsilon grouping loss when the shift product is polynomially
bounded in P. Constants depend only on rank, the fixed size exponent B and
epsilon, never on P, H, the tuple family or the sampled function. -/
theorem weighted_product_grouping_polynomial (r : ℕ) {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ H : ℕ, 0 < H → (H : ℝ) ≤ P^B →
      ∀ S : Finset (Fin r → ℕ), ∀ F : ℕ → ℝ,
      (∀ x ∈ S, tupleProduct x ∈ Finset.Icc 1 H) →
      (∀ n ∈ Finset.Icc 1 H, 0 ≤ F n) →
      (∑ x ∈ S, F (tupleProduct x)) ≤ C*P^ε*∑ n ∈ Finset.Icc 1 H, F n := by
  let δ : ℝ := ε/(B+1)
  have hB1 : 0 < B+1 := by linarith
  have hδ : 0 < δ := div_pos hε hB1
  have hBδ : B*δ ≤ ε := by
    have hid : δ*(B+1)=ε := div_mul_cancel₀ ε hB1.ne'
    nlinarith
  obtain ⟨C,hC,hgroup⟩ := weighted_product_grouping_rpow r hδ
  refine ⟨C,hC,?_⟩
  intro P hP H hH hHP S F hmap hF
  have hpower : (H : ℝ)^δ ≤ P^ε := by
    calc
      _ ≤ (P^B)^δ := Real.rpow_le_rpow (by positivity) hHP hδ.le
      _ = P^(B*δ) := (Real.rpow_mul (zero_le_one.trans hP) _ _).symm
      _ ≤ P^ε := Real.rpow_le_rpow_of_exponent_le hP hBδ
  exact (hgroup H hH S F hmap hF).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpower hC.le) (Finset.sum_nonneg hF))

/-- Coordinate bounds supply the product-range hypothesis directly. This
covers independent shift ranges as well as any further restricted subfamily. -/
theorem coordinate_bounds_product_range {r : ℕ} (x bounds : Fin r → ℕ)
    (hpos : ∀ i, 0 < x i) (hbound : ∀ i, x i ≤ bounds i) :
    tupleProduct x ∈ Finset.Icc 1 (tupleProduct bounds) := by
  apply Finset.mem_Icc.mpr
  constructor
  · exact Finset.prod_pos (fun i _ => hpos i)
  · exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hbound i)

#print axioms productFiber_card_le_divisors
#print axioms productFiber_card_le_rpow
#print axioms weighted_product_grouping_polynomial
end Waring.ProductMultiplicity
