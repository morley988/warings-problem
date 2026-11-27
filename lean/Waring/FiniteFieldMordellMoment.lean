import Waring.FiniteFieldMordellNewton
import Waring.External.GafniTao.WooleyFiniteMean

/-! # The literal complete coefficient moment for Mordell's estimate -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Waring.FiniteFieldMordell
open GafniTao

def vectorCharacterSum {ι : Type*} [Fintype ι] (q d : ℕ) [NeZero q]
    (v : ι → Fin d → ZMod q) (a : Fin d → ZMod q) : ℂ :=
  ∑ x,ZMod.stdAddChar (∑ j,a j*v x j)

theorem vectorCharacterSum_norm_sq {ι : Type*} [Fintype ι] (q d : ℕ) [NeZero q]
    (v : ι → Fin d → ZMod q) (a : Fin d → ZMod q) :
    ((‖vectorCharacterSum q d v a‖^2 : ℝ) : ℂ)=
      ∑ x : ι,∑ y : ι,∏ j,ZMod.stdAddChar (a j*(v x j-v y j)) := by
  classical
  unfold vectorCharacterSum
  rw [Complex.ofReal_pow,← Complex.mul_conj',map_sum,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [← AddChar.map_neg_eq_conj,← AddChar.map_add_eq_mul,← wooley_addChar_sum_eq_prod]
  congr 1
  rw [← sub_eq_add_neg,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vectorCharacterSum_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q d : ℕ) [NeZero q] (v : ι → Fin d → ZMod q) :
    (∑ a : Fin d → ZMod q,‖vectorCharacterSum q d v a‖^2)=
      (q : ℝ)^d*∑ x : ι,((Finset.univ.filter (fun y => v y=v x)).card : ℝ) := by
  classical
  have hc : ((∑ a : Fin d → ZMod q,‖vectorCharacterSum q d v a‖^2 : ℝ) : ℂ)=
      (q : ℂ)^d*∑ x : ι,((Finset.univ.filter (fun y => v y=v x)).card : ℂ) := by
    simp only [Complex.ofReal_sum,vectorCharacterSum_norm_sq]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x : ι,∑ y : ι,∑ a : Fin d → ZMod q,
          ∏ j,ZMod.stdAddChar (a j*(v x j-v y j)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ = ∑ x : ι,∑ y : ι,if v y=v x then (q : ℂ)^d else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        have hh := wooley_sum_grid_character q d (v x-v y)
        simpa only [Pi.sub_apply,sub_eq_zero,Nat.cast_pow,eq_comm] using hh
      _ = _ := by
        simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  exact_mod_cast hc

def coefficientSum (q d : ℕ) [NeZero q] (a : Fin d → ZMod q) : ℂ :=
  ∑ x : ZMod q,ZMod.stdAddChar (∑ j : Fin d,a j*x^(j.val+1))

def tuplePowers {q d : ℕ} (x : Fin d → ZMod q) : Fin d → ZMod q :=
  fun j => ∑ i,(x i)^(j.val+1)

theorem coefficientSum_pow (q d : ℕ) [NeZero q] (a : Fin d → ZMod q) :
    coefficientSum q d a ^ d=vectorCharacterSum q d tuplePowers a := by
  rw [coefficientSum,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  rw [← wooley_addChar_sum_eq_prod]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (Finset.mul_sum _ _ _).symm

theorem tuplePowers_fiber_card_le {p d : ℕ} [Fact p.Prime] (hdp : d<p)
    (x : Fin d → ZMod p) :
    (Finset.univ.filter (fun y : Fin d → ZMod p => tuplePowers y=tuplePowers x)).card ≤ d^d := by
  apply le_trans (Finset.card_le_card (t := powerSumFiber x) ?_)
    (zmod_powerSumFiber_card_le hdp x)
  intro y hy
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro j hj hjd
  have he := congrFun (Finset.mem_filter.mp hy).2 (⟨j-1,by omega⟩ : Fin d)
  simpa only [tuplePowers,Nat.sub_add_cancel hj] using he.symm

/-- The coefficient vector ranges over the complete finite field. The
moment is controlled by actual Newton collisions with no analytic premise. -/
theorem coefficientSum_moment_le {p d : ℕ} [Fact p.Prime] (hdp : d<p) :
    (∑ a : Fin d → ZMod p,‖coefficientSum p d a‖^(2*d)) ≤
      (d : ℝ)^d*(p : ℝ)^(2*d) := by
  have hpoint (a : Fin d → ZMod p) :
      ‖coefficientSum p d a‖^(2*d)=‖vectorCharacterSum p d tuplePowers a‖^2 := by
    rw [← coefficientSum_pow,norm_pow,← pow_mul,Nat.mul_comm d 2]
  simp_rw [hpoint]
  rw [vectorCharacterSum_gram]
  calc
    _ ≤ (p : ℝ)^d*∑ _x : Fin d → ZMod p,(d : ℝ)^d := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro x _
      exact_mod_cast tuplePowers_fiber_card_le hdp x
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
        ZMod.card,nsmul_eq_mul,Nat.cast_pow]
      rw [pow_mul]
      ring

#print axioms vectorCharacterSum_gram
#print axioms coefficientSum_moment_le
end Waring.FiniteFieldMordell
