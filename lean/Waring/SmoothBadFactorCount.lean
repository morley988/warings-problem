import Waring.PrimeSupportedCount
import Waring.PolicyCompletionSmoothDecomposition

/-!
# Counting the exceptional smooth factors in efficient differencing

For a nonzero derivative value D, a smooth integer without a block divisor
coprime to D has the form w*u with w <= M and all prime factors of u
dividing D. The exact image bound and uniform prime-supported count give
O(M*P^epsilon) such integers when D is polynomially bounded in P.
The exceptional D=0 case is deliberately not included in this estimate.
-/

noncomputable section
namespace Waring.SmoothBadFactorCount
open SmoothMoments PrimeSupportedCount

def badSmoothNumbers (P R M : ℝ) (D : ℕ) : Finset ℕ := by
  classical
  exact (smoothNumbers P R).filter (fun n =>
    ¬ ∃ d : ℕ, d ∈ CoefficientPower.coefficientBlock P R M ∧ d ∣ n ∧ d.Coprime D)

/-- The exceptional integers lie in an actual finite multiplication image. -/
theorem badSmoothNumbers_subset_image {P R M : ℝ} {D : ℕ}
    (hM : 1 ≤ M) :
    badSmoothNumbers P R M D ⊆
      ((Finset.Icc 1 ⌊M⌋₊) ×ˢ supportedNumbers ⌊P⌋₊ D).image
        (fun x : ℕ × ℕ => x.1*x.2) := by
  classical
  intro n hn
  obtain ⟨hn, hbad⟩ := Finset.mem_filter.mp hn
  obtain hsplit := smooth_coprime_window_or_supported_quotient (b := D) hn hM
  rcases hsplit with ⟨w,u,hnu,hwM,hu⟩ | hgood
  · have hnpos : 0 < n := by
      have h := (mem_smoothNumbers.mp hn).1.1
      omega
    have hwu : 0 < w*u := by rw [← hnu]; exact hnpos
    have hwpos : 0 < w := by
      by_contra h
      have hw0 : w = 0 := by omega
      simp [hw0] at hwu
    have hupos : 0 < u := by
      by_contra h
      have hu0 : u = 0 := by omega
      simp [hu0] at hwu
    have huP : u ≤ ⌊P⌋₊ :=
      (Nat.le_of_dvd hnpos ⟨w, by rw [hnu, mul_comm]⟩).trans
        (mem_smoothNumbers.mp hn).1.2
    apply Finset.mem_image.mpr
    refine ⟨(w,u), Finset.mem_product.mpr ⟨?_,?_⟩, hnu.symm⟩
    · exact Finset.mem_Icc.mpr ⟨hwpos, Nat.le_floor hwM⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hupos,huP⟩,hu⟩
  · exact (hbad hgood).elim

theorem badSmoothNumbers_card_le {P R M : ℝ} {D : ℕ} (hM : 1 ≤ M) :
    (badSmoothNumbers P R M D).card ≤
      ⌊M⌋₊ * (supportedNumbers ⌊P⌋₊ D).card := by
  classical
  calc
    (badSmoothNumbers P R M D).card ≤
        (((Finset.Icc 1 ⌊M⌋₊) ×ˢ supportedNumbers ⌊P⌋₊ D).image
          (fun x : ℕ × ℕ => x.1*x.2)).card :=
      Finset.card_le_card (badSmoothNumbers_subset_image hM)
    _ ≤ ((Finset.Icc 1 ⌊M⌋₊) ×ˢ supportedNumbers ⌊P⌋₊ D).card :=
      Finset.card_image_le
    _ = ⌊M⌋₊ * (supportedNumbers ⌊P⌋₊ D).card := by
      simp only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]

/-- Uniform epsilon estimate for the actual exceptional set, independent
of the smoothness cutoff R and of the particular nonzero integer D. -/
theorem badSmoothNumbers_card_le_rpow {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P R M : ℝ, 1 ≤ P → 1 ≤ M →
      ∀ D : ℕ, 0 < D → (D : ℝ) ≤ P^B →
      ((badSmoothNumbers P R M D).card : ℝ) ≤ C * M * P^ε := by
  obtain ⟨C,hC,hbound⟩ := supportedNumbers_polynomial_scale
    (A := (1 : ℝ)) (by norm_num) hB hε
  refine ⟨C,hC,?_⟩
  intro P R M hP hM D hD hDP
  have hsupport : ((supportedNumbers ⌊P⌋₊ D).card : ℝ) ≤ C*P^ε := by
    simpa only [Real.rpow_one] using hbound P hP D hD hDP
  have hfinite : ((badSmoothNumbers P R M D).card : ℝ) ≤
      (⌊M⌋₊ : ℝ) * ((supportedNumbers ⌊P⌋₊ D).card : ℝ) := by
    exact_mod_cast badSmoothNumbers_card_le (D := D) (P := P) (R := R) hM
  calc
    ((badSmoothNumbers P R M D).card : ℝ) ≤
        (⌊M⌋₊ : ℝ) * ((supportedNumbers ⌊P⌋₊ D).card : ℝ) := hfinite
    _ ≤ M * ((supportedNumbers ⌊P⌋₊ D).card : ℝ) :=
      mul_le_mul_of_nonneg_right (Nat.floor_le (zero_le_one.trans hM)) (by positivity)
    _ ≤ M * (C * P^ε) :=
      mul_le_mul_of_nonneg_left hsupport (zero_le_one.trans hM)
    _ = C * M * P^ε := by ring

#print axioms badSmoothNumbers_card_le
#print axioms badSmoothNumbers_card_le_rpow

end Waring.SmoothBadFactorCount
