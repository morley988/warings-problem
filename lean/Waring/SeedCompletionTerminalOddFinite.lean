import Waring.SeedCompletionTerminalCurves
import Waring.SeedCompletionTerminalPhase

/-! # Center divisibility and same-center polynomial collisions for odd residual degree -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalOddFinite
open Polynomial SeedCompletionTerminalPhase SeedCompletionTerminalCurves
open IntegerDifferencePolynomial PolicyCompletionMajorFamily

theorem center_dvd_phase {j : ℕ} (k : ℕ) (h m : Fin j → ℕ)
    (hm : ∀ i, 0 < m i) (hodd : Odd (k+j)) (z : ℕ) : (z : ℤ) ∣ phase k h m z := by
  have hp := realPolynomial_parity k h m hm (0 : ℝ)
  simp only [neg_zero,hodd.neg_one_pow,neg_one_mul] at hp
  have hzR : (phase k h m 0 : ℝ)=0 := by
    rw [← realPolynomial_eval k h m 0]
    norm_num only [Nat.cast_zero]
    linarith
  have hz : phase k h m 0=0 := by exact_mod_cast hzR
  have hd := Polynomial.sub_dvd_eval_sub (z : ℤ) 0
    (powerPolynomial k (naturalParameters h m))
  change (z : ℤ)-0 ∣ phase k h m z-phase k h m 0 at hd
  simpa only [hz,sub_zero] using hd

theorem unequal_evaluations_card_le (f g : Polynomial ℝ) (hf : f ≠ g) (D : ℕ)
    (hfd : f.natDegree ≤ D) (hgd : g.natDegree ≤ D) (Z : Finset ℕ) :
    (Z.filter (fun z : ℕ => f.eval (z : ℝ)=g.eval (z : ℝ))).card ≤ D := by
  classical
  have hne : f-g ≠ 0 := sub_ne_zero.mpr hf
  have hc : (Z.filter (fun z : ℕ => f.eval (z : ℝ)=g.eval (z : ℝ))).card ≤
      (f-g).roots.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun z : ℕ => (z : ℝ))
    · intro z hz
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hne).mpr
      rw [Polynomial.IsRoot,Polynomial.eval_sub,(Finset.mem_filter.mp hz).2,sub_self]
    · exact Nat.cast_injective.injOn
  exact hc.trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans ((Polynomial.natDegree_sub_le _ _).trans
      (max_le hfd hgd))))

def coefficientPairs {ι : Type*} (B : Finset ι) (f : ι → ℕ → ℤ) (z : ℕ) :=
  (B ×ˢ B).filter (fun mn => f mn.1 z=f mn.2 z)

theorem same_center_family_bound {ι : Type*} (B : Finset ι) (Z : Finset ℕ)
    (f : ι → ℕ → ℤ) (F : ι → Polynomial ℝ) (D : ℕ)
    (hdeg : ∀ m ∈ B, (F m).natDegree ≤ D)
    (heval : ∀ m ∈ B, ∀ z : ℕ, (F m).eval (z : ℝ)=(f m z : ℝ)) :
    (∑ z ∈ Z, (coefficientPairs B f z).card) ≤
      Z.card*(samePolynomialPairs B F).card+D*B.card^2 := by
  classical
  have hpoint (m : ι) (hm : m ∈ B) (n : ι) (hn : n ∈ B) :
      (Z.filter (fun z => f m z=f n z)).card ≤
        (if F m=F n then Z.card else 0)+D := by
    by_cases he : F m=F n
    · rw [if_pos he]
      exact (Finset.card_filter_le _ _).trans (Nat.le_add_right _ _)
    · rw [if_neg he,zero_add]
      have heq : Z.filter (fun z => f m z=f n z)=
          Z.filter (fun z : ℕ => (F m).eval (z : ℝ)=(F n).eval (z : ℝ)) := by
        apply Finset.filter_congr
        intro z hz
        rw [heval m hm,heval n hn]
        exact (Int.cast_injective (α := ℝ)).eq_iff.symm
      rw [heq]
      exact unequal_evaluations_card_le (F m) (F n) he D (hdeg m hm) (hdeg n hn) Z
  have hsum : (∑ z ∈ Z, (coefficientPairs B f z).card)=
      ∑ m ∈ B, ∑ n ∈ B, (Z.filter (fun z => f m z=f n z)).card := by
    simp only [coefficientPairs,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_comm]
  have hdiag : (∑ m ∈ B, ∑ n ∈ B, if F m=F n then Z.card else 0)=
      Z.card*(samePolynomialPairs B F).card := by
    simp only [samePolynomialPairs,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product,
      Finset.mul_sum,mul_ite,mul_one,mul_zero]
  rw [hsum]
  calc
    _ ≤ ∑ m ∈ B, ∑ n ∈ B, ((if F m=F n then Z.card else 0)+D) := by
      exact Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => hpoint m hm n hn))
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
      rw [hdiag]
      ring

#print axioms center_dvd_phase
#print axioms same_center_family_bound
end Waring.SeedCompletionTerminalOddFinite
