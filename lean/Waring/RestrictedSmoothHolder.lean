import Waring.RestrictedSmoothCoprimeBlocks
import Mathlib.Analysis.MeanInequalities

/-! # Pointwise Holder reduction for the actual coprime blocks -/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothFactorization
open SmoothMoments

theorem norm_sum_pow_le_card {ι : Type*} (A : Finset ι) (f : ι → ℂ)
    {s : ℕ} (hs : 1 ≤ s) :
    ‖∑ a ∈ A, f a‖^s ≤ (A.card : ℝ)^(s-1)*∑ a ∈ A, ‖f a‖^s := by
  have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg A (f := fun a => ‖f a‖)
    (p := (s : ℝ)) (by exact_mod_cast hs) (fun a _ => norm_nonneg (f a))
  have he : (s : ℝ)-1=((s-1 : ℕ) : ℝ) := by rw [Nat.cast_sub hs,Nat.cast_one]
  rw [he] at hh
  simp only [Real.rpow_natCast] at hh
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) s).trans hh

theorem phase_mul_scale (k m n : ℕ) (α : ℝ) :
    phase k (m*n) α=phase k n ((m : ℝ)^k*α) := by
  unfold phase
  congr 2
  push_cast
  rw [mul_pow]
  ring

def mixedPrimeWeyl (k q π : ℕ) (X R α : ℝ) : ℂ :=
  ∑ p ∈ mixedPrimeDomain X R (fun l => l ∣ q) (fun l => l ≤ π),
    phase k (p.1*p.2) α

def largeCoprimeSum (k q : ℕ) (P R M α : ℝ) : ℂ :=
  ∑ p ∈ largeCoprimeDomain q P R M, phase k (p.1*p.2) α

theorem smoothWeyl_small_large (k q : ℕ) {P R M α : ℝ} (hM : 0 ≤ M) :
    smoothWeyl k P R α=smallCoprimeSum k q P R M α+largeCoprimeSum k q P R M α := by
  classical
  rw [smoothWeyl_supported_coprime k q]
  have h := Finset.sum_filter_add_sum_filter_not (supportedCoprimeDomain q P R)
    (fun p : ℕ × ℕ => p.2 ≤ ⌊M⌋₊) (fun p => phase k (p.1*p.2) α)
  simpa only [smallCoprimeSum,largeCoprimeSum,smallCoprimeDomain,largeCoprimeDomain,
    Nat.le_floor_iff hM,not_le] using h.symm

theorem largeCoprimeSum_blocks (k q : ℕ) {P R M α : ℝ}
    (hP : 0 ≤ P) (hM : 1 ≤ M) :
    largeCoprimeSum k q P R M α =
      ∑ b ∈ coprimeBlocks q M R,
        mixedPrimeWeyl k q b.1 (P/(b.2 : ℝ)) R ((b.2 : ℝ)^k*α) := by
  rw [largeCoprimeSum,largeCoprime_sum_blocks hP hM]
  apply Finset.sum_congr rfl
  intro b hb
  unfold mixedPrimeWeyl
  apply Finset.sum_congr rfl
  intro p hp
  rw [show p.1*(b.2*p.2)=b.2*(p.1*p.2) by ring,phase_mul_scale]

theorem coprimeBlocks_card_le (q : ℕ) {M R : ℝ} (hM : 1 ≤ M) (hMR : 0 ≤ M*R) :
    ((coprimeBlocks q M R).card : ℝ) ≤ M*R := by
  have hc := Finset.card_filter_le (orderedBlocks M R) (fun p : ℕ × ℕ => p.2.Coprime q)
  exact (Nat.cast_le.mpr hc).trans (orderedBlocks_card_le hM hMR)

theorem largeCoprimeSum_holder (k q : ℕ) {s : ℕ} (hs : 1 ≤ s)
    {P R M α : ℝ} (hP : 0 ≤ P) (hM : 1 ≤ M) (hMR : 0 ≤ M*R) :
    ‖largeCoprimeSum k q P R M α‖^s ≤
      (M*R)^(s-1)*∑ b ∈ coprimeBlocks q M R,
        ‖mixedPrimeWeyl k q b.1 (P/(b.2 : ℝ)) R ((b.2 : ℝ)^k*α)‖^s := by
  rw [largeCoprimeSum_blocks k q hP hM]
  apply (norm_sum_pow_le_card _ _ hs).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (coprimeBlocks_card_le q hM hMR) _)
    (Finset.sum_nonneg (fun _ _ => by positivity))

/-- The source pointwise reduction, retaining its actual small branch.
Both finite sums use the original coprime and prime-restricted domains. -/
theorem smoothWeyl_coprime_block_bound (k q : ℕ) {s : ℕ} (hs : 1 ≤ s)
    {P R M α : ℝ} (hP : 0 ≤ P) (hM : 1 ≤ M) (hMR : 0 ≤ M*R) :
    ‖smoothWeyl k P R α‖^s ≤ (2 : ℝ)^(s-1)*
      (‖smallCoprimeSum k q P R M α‖^s+
        (M*R)^(s-1)*∑ b ∈ coprimeBlocks q M R,
          ‖mixedPrimeWeyl k q b.1 (P/(b.2 : ℝ)) R ((b.2 : ℝ)^k*α)‖^s) := by
  rw [smoothWeyl_small_large k q (zero_le_one.trans hM)]
  calc
    _ ≤ (‖smallCoprimeSum k q P R M α‖+‖largeCoprimeSum k q P R M α‖)^s :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _
    _ ≤ (2 : ℝ)^(s-1)*(‖smallCoprimeSum k q P R M α‖^s+
        ‖largeCoprimeSum k q P R M α‖^s) := add_pow_le (norm_nonneg _) (norm_nonneg _) _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add_left (largeCoprimeSum_holder k q hs hP hM hMR) _) (by positivity)

#print axioms smoothWeyl_coprime_block_bound
end Waring.RestrictedSmoothFactorization
