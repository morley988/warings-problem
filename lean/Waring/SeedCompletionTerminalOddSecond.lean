import Waring.SeedCompletionTerminalOddFinite
import Waring.SeedCompletionTerminalSecond

/-! # The sharp second-moment reduction for every odd residual source degree -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalOddSecond
open SeedCompletionTerminalPhase SeedCompletionTerminalCurves SeedCompletionTerminalOddFinite
open SeedCompletionTerminalSecond SeedCompletionProductGrouping AuxiliaryL2Grouping

theorem odd_source_second_moment {k j : ℕ} (hjk : j < k) (hodd : Odd (k+j))
    {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ H B : Finset (Fin j → ℕ), (∀ h ∈ H, ∀ i, 0 < h i) →
      (∀ m ∈ B, ∀ i, 0 < m i) → ∀ Z : Finset ℕ, (∀ z ∈ Z, 0 < z) →
      (∀ h ∈ H, ∀ m ∈ B, ∀ z ∈ Z, ((phase k h m z).natAbs : ℝ) ≤ P^L) →
      sourceSecondMoment k H B Z ≤
        C*P^ε*((Z.card : ℝ)*(∑ h ∈ H, ((samePolynomialPairs B (realPolynomial k h)).card : ℝ))+
          ((k-j : ℕ) : ℝ)*(H.card : ℝ)*(B.card : ℝ)^2) := by
  obtain ⟨C,hC,hbound⟩ := second_moment_divisor_product (j+1) hL hε
  refine ⟨C,hC,?_⟩
  intro P hP H B hH hB Z hZ hsize
  let key : (Fin j → ℕ) × ℕ → Fin (j+1) → ℕ := fun hz => Fin.cons hz.2 hz.1
  have hkey : Function.Injective key := by
    intro hz gw he
    apply Prod.ext
    · funext i
      exact congrFun he i.succ
    · exact congrFun he 0
  have hb := hbound P hP ((Fin j → ℕ) × ℕ) (Fin j → ℕ) (H ×ˢ Z) B
    (fun hz m => phase k hz.1 m hz.2) key hkey.injOn
    (by
      intro hz hhz m hm
      obtain ⟨hh,hz⟩ := Finset.mem_product.mp hhz
      exact ⟨(phase_pos hjk _ _ (hH _ hh) (hB _ hm) (hZ _ hz)).ne',hsize _ hh _ hm _ hz⟩)
    (by
      intro hz hhz m hm i
      refine Fin.cases ?_ (fun t => ?_) i
      · exact center_dvd_phase k hz.1 m (hB _ hm) hodd hz.2
      · exact height_dvd_phase k hz.1 m (hB _ hm) hz.2 t)
  have hsums (α : ℝ) :
      (∑ x ∈ H ×ˢ (B ×ˢ Z), fourier (phase k x.1 x.2.1 x.2.2) (α : AddCircle (1 : ℝ))) =
      ∑ x ∈ (H ×ˢ Z) ×ˢ B, fourier (phase k x.1.1 x.2 x.1.2) (α : AddCircle (1 : ℝ)) := by
    simp only [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro h hh
    exact Finset.sum_comm
  have hmoment : sourceSecondMoment k H B Z =
      ∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ (H ×ˢ Z) ×ˢ B, fourier (phase k x.1.1 x.2 x.1.2) (α : AddCircle (1 : ℝ))‖^2 := by
    unfold sourceSecondMoment
    simp_rw [hsums]
  rw [hmoment]
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.sum_product]
  calc
    _ ≤ ∑ h ∈ H, ((Z.card : ℝ)*((samePolynomialPairs B (realPolynomial k h)).card : ℝ)+
        ((k-j : ℕ) : ℝ)*(B.card : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro h hh
      have hc := same_center_family_bound B Z (phase k h) (realPolynomial k h) (k-j)
        (fun m hm => (realPolynomial_natDegree hjk.le h m (hH _ hh) (hB _ hm)).le)
        (fun m _ z => realPolynomial_eval k h m z)
      exact_mod_cast hc
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring

#print axioms odd_source_second_moment
end Waring.SeedCompletionTerminalOddSecond
