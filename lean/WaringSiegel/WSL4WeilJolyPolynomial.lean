import WaringSiegel.WSL4WeilHensel
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1000000

/-- The integral numerator in Joly's characteristic-exponent construction. -/
def jolyNumerator (k : ℕ) [NeZero k] : ℤ[X] :=
  ∑ a : ZMod k, ((X : ℤ[X])^k-(X-C (a.val : ℤ))^k)

/-- Its derivative after cancelling the factor k. -/
def jolyDerivative (k : ℕ) [NeZero k] : ℤ[X] :=
  ∑ a : ZMod k, ((X : ℤ[X])^(k-1)-(X-C (a.val : ℤ))^(k-1))

theorem jolyNumerator_degree_lt (k : ℕ) [NeZero k] :
    (jolyNumerator k).degree < k := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe k)).mpr
  intro a ha
  have he : degree ((X-C (a.val : ℤ))^k)=(k : WithBot ℕ) := by
    rw [degree_pow,degree_X_sub_C]
    simp
  have h := degree_sub_lt (p := (X : ℤ[X])^k)
    (q := (X-C (a.val : ℤ))^k) (by rw [degree_X_pow,he])
    (pow_ne_zero _ X_ne_zero)
    (by rw [(monic_X.pow k).leadingCoeff,((monic_X_sub_C _).pow k).leadingCoeff])
  simpa only [degree_X_pow] using h

theorem jolyNumerator_map_eq_zero (k : ℕ) [Fact k.Prime] (hk : 2<k) :
    (jolyNumerator k).map (Int.castRingHom (ZMod k))=0 := by
  have hs : ∑ a : ZMod k, a=0 := by
    simpa only [pow_one,ZMod.card] using
      FiniteField.sum_pow_lt_card_sub_one (ZMod k) 1 (by rw [ZMod.card]; omega)
  simp only [jolyNumerator,Polynomial.map_sum,Polynomial.map_sub,Polynomial.map_pow,
    map_X,map_C,Int.coe_castRingHom,Int.cast_natCast,ZMod.natCast_zmod_val]
  simp only [sub_pow_char,← C_pow,ZMod.pow_card,sub_sub_cancel]
  rw [← map_sum,hs,map_zero]

theorem jolyNumerator_dvd (k : ℕ) [Fact k.Prime] (hk : 2<k) :
    C (k : ℤ) ∣ jolyNumerator k := by
  rw [C_dvd_iff_dvd_coeff]
  intro n
  apply (CharP.intCast_eq_zero_iff (ZMod k) k _).mp
  have h := congrArg (fun f : (ZMod k)[X] => f.coeff n)
    (jolyNumerator_map_eq_zero k hk)
  simpa only [coeff_map,Int.coe_castRingHom,coeff_zero] using h

theorem jolyNumerator_derivative (k : ℕ) [NeZero k] :
    (jolyNumerator k).derivative=C (k : ℤ)*jolyDerivative k := by
  simp only [jolyNumerator,jolyDerivative,derivative_sum,derivative_sub,derivative_pow,
    derivative_X,derivative_C,sub_zero,mul_one,Finset.mul_sum,mul_sub]

end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.jolyNumerator_dvd
