import WaringSiegel.WSL4WeilJolyPolynomial
import Mathlib.Algebra.Polynomial.BigOperators

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1000000

theorem primeField_sum_pred_power (k : ℕ) [Fact k.Prime] :
    (∑ a : ZMod k, a^(k-1)) = -1 := by
  have he (a : ZMod k) : a^(k-1)=1-(if a=0 then 1 else 0) := by
    by_cases ha : a=0 <;> simp [ZMod.pow_card_sub_one,ha]
  simp_rw [he,Finset.sum_sub_distrib]
  simp [ZMod.card]

theorem jolyDerivative_natDegree_le (k : ℕ) [NeZero k] :
    (jolyDerivative k).natDegree≤k-1 := by
  apply natDegree_sum_le_of_forall_le
  intro a ha
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · rw [natDegree_X_pow]
  · rw [natDegree_pow,natDegree_X_sub_C,mul_one]

theorem jolyDerivative_map_eq_one (k : ℕ) [Fact k.Prime] :
    (jolyDerivative k).map (Int.castRingHom (ZMod k))=1 := by
  let D := (jolyDerivative k).map (Int.castRingHom (ZMod k))
  have he (x : ZMod k) : D.eval x=1 := by
    have hs : (∑ a : ZMod k,(x-a)^(k-1)) = -1 := by
      have ht := (Equiv.subLeft x).sum_comp (fun y : ZMod k => y^(k-1))
      change (∑ a : ZMod k,(x-a)^(k-1))=∑ a : ZMod k,a^(k-1) at ht
      rw [ht]
      exact primeField_sum_pred_power k
    simp only [D,jolyDerivative,Polynomial.map_sum,Polynomial.map_sub,Polynomial.map_pow,
      map_X,map_C,Int.coe_castRingHom,Int.cast_natCast,ZMod.natCast_zmod_val,
      eval_finset_sum,eval_sub,eval_pow,eval_X,eval_C]
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,ZMod.card,
      nsmul_eq_mul,ZMod.natCast_self,zero_mul,hs]
    ring
  have hd : (D-1).natDegree< Fintype.card (ZMod k) := by
    have hD : D.natDegree≤k-1 :=
      natDegree_map_le.trans (jolyDerivative_natDegree_le k)
    have h := (natDegree_sub_le D 1).trans (max_le hD (by simp))
    rw [ZMod.card]
    exact h.trans_lt (Nat.sub_lt (Fact.out : k.Prime).pos (by omega))
  have hz : D-1=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (D-1) Function.injective_id (by intro x; simp [he]) hd
  exact sub_eq_zero.mp hz

theorem primePolynomial_affine_of_derivative_one
    (k : ℕ) [Fact k.Prime] (f : (ZMod k)[X]) (hf : f.natDegree<k)
    (hd : f.derivative=1) : f=X+C (f.coeff 0) := by
  ext n
  rcases n with _|n
  · simp
  have he := congrArg (fun p : (ZMod k)[X] => p.coeff n) hd
  change f.derivative.coeff n=(1 : (ZMod k)[X]).coeff n at he
  rw [coeff_derivative] at he
  by_cases hn : n=0
  · subst n
    simpa using he
  · have hn1 : n+1≠1 := by omega
    have hrhs : (X+C (f.coeff 0)).coeff (n+1)=0 := by
      simp [coeff_X,hn,hn1,Ne.symm hn1]
    rw [hrhs]
    by_cases hnk : n+1<k
    · have hcast : ((n+1:ℕ) : ZMod k)≠0 := by
        intro hz
        exact (Nat.not_dvd_of_pos_of_lt (by omega) hnk)
          ((CharP.cast_eq_zero_iff (ZMod k) k _).mp hz)
      have hncoeff : (1 : (ZMod k)[X]).coeff n=0 := by
        rw [coeff_one]
        simp [hn,Ne.symm hn]
      rw [hncoeff] at he
      exact (mul_eq_zero.mp he).resolve_right (by simpa using hcast)
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hf (show k≤n+1 by omega))


end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.jolyDerivative_map_eq_one
#print axioms WaringSiegel.WSL4Weil.primePolynomial_affine_of_derivative_one
