import Waring.SeedCompletionCurveParityFamilies
import Waring.SeedCompletionProductGrouping

/-!
# Terminal curve energy retaining the full polynomial diagonal

The diagonal contribution is its exact pair count. This permits the
weighted sparse system to control it after summing over common heights.
-/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalCurves
open SeedCompletionCurveFamilies SeedCompletionCurveParityFamilies
open SeedCompletionProductGrouping AuxiliaryL2Grouping

def samePolynomialPairs {ι : Type*} (B : Finset ι) (F : ι → Polynomial ℝ) :=
  (B ×ˢ B).filter (fun mn => F mn.1 = F mn.2)

theorem family_collision_card_bound_diagonal {ι : Type*} {σ : ℝ}
    (f : ι → ℕ → ℤ) (F : ι → Polynomial ℝ) (B : Finset ι) (Z : Finset ℕ)
    (D : ℕ) (hD : 0 < D)
    (hdeg : ∀ m ∈ B, (F m).natDegree=D)
    (hlead : ∀ m ∈ B, ∀ n ∈ B, (F m).leadingCoeff=(F n).leadingCoeff)
    (hσ : σ^2=1) (hpar : ∀ m ∈ B, ∀ t : ℝ, (F m).eval (-t)=σ*(F m).eval t)
    (hmono : ∀ m ∈ B, StrictMono (f m))
    (heval : ∀ m ∈ B, ∀ z : ℕ, (F m).eval (z : ℝ)=(f m z : ℝ))
    (P : ℝ) (hP : 1 ≤ P) (hZ : ∀ z ∈ Z, (z : ℝ) ≤ P) :
    ((collisionPairs (B ×ˢ Z) (fun mz => f mz.1 mz.2)).card : ℝ) ≤
      (Z.card : ℝ)*((samePolynomialPairs B F).card : ℝ) +
        (B.card : ℝ)^2*((D : ℝ)*(8*(D : ℝ)^2+3)*P^(2/3 : ℝ)) := by
  classical
  let T : ℝ := (D : ℝ)*(8*(D : ℝ)^2+3)*P^(2/3 : ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpair (m : ι) (hm : m ∈ B) (n : ι) (hn : n ∈ B) :
      ((centerPairs f m n Z).card : ℝ) ≤ (if F m=F n then (Z.card : ℝ) else 0)+T := by
    by_cases he : F m=F n
    · rw [if_pos he,centerPairs_equal f F m n Z (hmono n hn)
        (heval m hm) (heval n hn) he]
      linarith
    · rw [if_neg he,zero_add]
      exact centerPairs_unequal_parity f F m n Z D hD (hdeg m hm) (hdeg n hn)
        (hlead m hm n hn) hσ (hpar m hm) (hpar n hn) (hmono m hm) (hmono n hn)
        (heval m hm) (heval n hn) he P hP hZ
  have hdiag : (∑ m ∈ B, ∑ n ∈ B, if F m=F n then (Z.card : ℝ) else 0) =
      (Z.card : ℝ)*((samePolynomialPairs B F).card : ℝ) := by
    simp only [samePolynomialPairs,Finset.card_eq_sum_ones,Nat.cast_sum,Nat.cast_ite,
      Nat.cast_one,Nat.cast_zero,Finset.sum_filter,Finset.sum_product,Finset.mul_sum]
    simp only [mul_ite,mul_one,mul_zero]
  rw [collision_card,Nat.cast_sum]
  calc
    _ ≤ ∑ m ∈ B, ∑ n ∈ B, ((if F m=F n then (Z.card : ℝ) else 0)+T) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun n hn => hpair m hm n hn)
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
      rw [hdiag]
      dsimp [T]
      ring

theorem second_moment_diagonal_and_curve {j : ℕ} {L ε : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ (ι : Type*) (H : Finset (Fin j → ℕ)) (B : Finset ι) (Z : Finset ℕ)
        (f : (Fin j → ℕ) → ι → ℕ → ℤ)
        (F : (Fin j → ℕ) → ι → Polynomial ℝ)
        (D : ℕ) (σ : ℝ), 0 < D → σ^2=1 →
      (∀ h ∈ H, ∀ m ∈ B, (F h m).natDegree=D) →
      (∀ h ∈ H, ∀ m ∈ B, ∀ n ∈ B, (F h m).leadingCoeff=(F h n).leadingCoeff) →
      (∀ h ∈ H, ∀ m ∈ B, ∀ t : ℝ, (F h m).eval (-t)=σ*(F h m).eval t) →
      (∀ h ∈ H, ∀ m ∈ B, StrictMono (f h m)) →
      (∀ h ∈ H, ∀ m ∈ B, ∀ z : ℕ, (F h m).eval (z : ℝ)=(f h m z : ℝ)) →
      (∀ z ∈ Z, (z : ℝ) ≤ P) →
      (∀ h ∈ H, ∀ m ∈ B, ∀ z ∈ Z, f h m z ≠ 0 ∧ ((f h m z).natAbs : ℝ) ≤ P^L) →
      (∀ h ∈ H, ∀ m ∈ B, ∀ z ∈ Z, ∀ i, (h i : ℤ) ∣ f h m z) →
      (∫ α in (0 : ℝ)..1, ‖∑ x ∈ H ×ˢ (B ×ˢ Z),
        fourier (f x.1 x.2.1 x.2.2) (α : AddCircle (1 : ℝ))‖^2) ≤
      C*P^ε*((Z.card : ℝ)*(∑ h ∈ H, ((samePolynomialPairs B (F h)).card : ℝ)) +
        (H.card : ℝ)*(B.card : ℝ)^2*((D : ℝ)*(8*(D : ℝ)^2+3)*P^(2/3 : ℝ))) := by
  obtain ⟨C,hC,hbound⟩ := second_moment_divisor_product j hL hε
  refine ⟨C,hC,?_⟩
  intro P hP ι H B Z f F D σ hD hσ hdeg hlead hpar hmono heval hZ hsize hdvd
  have hb := hbound P hP (Fin j → ℕ) (ι×ℕ) H (B ×ˢ Z)
    (fun h mz => f h mz.1 mz.2) id (Function.injective_id.injOn)
    (fun h hh mz hmz => hsize h hh mz.1 (Finset.mem_product.mp hmz).1
      mz.2 (Finset.mem_product.mp hmz).2)
    (fun h hh mz hmz i => hdvd h hh mz.1 (Finset.mem_product.mp hmz).1
      mz.2 (Finset.mem_product.mp hmz).2 i)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ h ∈ H, ((Z.card : ℝ)*((samePolynomialPairs B (F h)).card : ℝ) +
        (B.card : ℝ)^2*((D : ℝ)*(8*(D : ℝ)^2+3)*P^(2/3 : ℝ))) := by
      exact Finset.sum_le_sum (fun h hh => family_collision_card_bound_diagonal
        (f h) (F h) B Z D hD (hdeg h hh) (hlead h hh) hσ (hpar h hh)
        (hmono h hh) (heval h hh) P hP hZ)
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring

#print axioms family_collision_card_bound_diagonal
#print axioms second_moment_diagonal_and_curve
end Waring.SeedCompletionTerminalCurves
