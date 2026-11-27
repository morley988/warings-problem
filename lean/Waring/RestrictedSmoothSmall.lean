import Waring.RestrictedSmoothSums

/-! # The actual short coprime branch of the restricted smooth sum -/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothFactorization
open SmoothMoments PrimeSupportedCount

def smallCoprimeDomain (q : ℕ) (P R M : ℝ) : Finset (ℕ × ℕ) :=
  (supportedCoprimeDomain q P R).filter (fun p => p.2 ≤ ⌊M⌋₊)

def smallCoprimeSum (k q : ℕ) (P R M α : ℝ) : ℂ :=
  ∑ p ∈ smallCoprimeDomain q P R M, phase k (p.1*p.2) α

theorem smallCoprimeDomain_subset (q : ℕ) (P R M : ℝ) :
    smallCoprimeDomain q P R M ⊆ supportedNumbers ⌊P⌋₊ q ×ˢ Finset.Icc 1 ⌊M⌋₊ := by
  classical
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp,hM⟩
  rcases Finset.mem_filter.mp hp with ⟨hp,_,hs,_⟩
  rcases Finset.mem_product.mp hp with ⟨hu,hv⟩
  have hu := mem_smoothNumbers.mp hu
  have hv := mem_smoothNumbers.mp hv
  exact Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hu.1,hs⟩,
      Finset.mem_Icc.mpr ⟨hv.1.1,hM⟩⟩

theorem smallCoprimeDomain_card (q : ℕ) (P R M : ℝ) :
    (smallCoprimeDomain q P R M).card ≤ (supportedNumbers ⌊P⌋₊ q).card*⌊M⌋₊ := by
  have h := Finset.card_le_card (smallCoprimeDomain_subset q P R M)
  simpa only [Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel] using h

theorem norm_smallCoprimeSum_le_card (k q : ℕ) (P R M α : ℝ) :
    ‖smallCoprimeSum k q P R M α‖ ≤ (smallCoprimeDomain q P R M).card := by
  unfold smallCoprimeSum
  calc
    _ ≤ ∑ p ∈ smallCoprimeDomain q P R M, ‖phase k (p.1*p.2) α‖ := norm_sum_le _ _
    _ = _ := by simp

/-- The short branch is uniformly O(P^epsilon M), with its original
coprime and supported-factor definition and q in a polynomial range. -/
theorem smallCoprimeSum_bound {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ P^B → ∀ R M α : ℝ, 0 ≤ M → ∀ k : ℕ,
      ‖smallCoprimeSum k q P R M α‖ ≤ C*P^ε*M := by
  obtain ⟨C,hC,hbound⟩ := supportedNumbers_polynomial_scale (A := 1) (by norm_num) hB hε
  refine ⟨C,hC,?_⟩
  intro P hP q hq hqP R M α hM k
  have h := hbound P hP q hq hqP
  rw [Real.rpow_one] at h
  calc
    _ ≤ ((smallCoprimeDomain q P R M).card : ℝ) := norm_smallCoprimeSum_le_card ..
    _ ≤ ((supportedNumbers ⌊P⌋₊ q).card : ℝ)*(⌊M⌋₊ : ℝ) := by
      exact_mod_cast smallCoprimeDomain_card q P R M
    _ ≤ (C*P^ε)*M := mul_le_mul h (Nat.floor_le hM) (Nat.cast_nonneg _)
      (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hP) _))

#print axioms smallCoprimeSum_bound
end Waring.RestrictedSmoothFactorization
