import Waring.EndgameCompletionSingularCRT

/-! # Exact reduction of imprimitive product singular terms -/

noncomputable section
open scoped BigOperators
namespace Waring.EndgameCompletion

def residueReduction (d q : ℕ) : ZMod (d*q) →+* ZMod q :=
  ZMod.castHom (dvd_mul_left q d) (ZMod q)

theorem residueReduction_eq_val (d q : ℕ) [NeZero d] [NeZero q] (a : ZMod (d*q)) :
    residueReduction d q a=(a.val : ZMod q) := by
  exact ZMod.cast_eq_val a

theorem sum_residueReduction (d q : ℕ) [NeZero d] [NeZero q] (F : ZMod q→ℂ) :
    (∑ x : ZMod (d*q),F (residueReduction d q x))=(d : ℂ)*∑ y : ZMod q,F y := by
  rw [sum_zmod_eq_sum_range]
  simp only [map_natCast]
  have hp : Function.Periodic (fun n : ℕ=>F (n : ZMod q)) q := by
    intro n
    simp only [Nat.cast_add,ZMod.natCast_self,add_zero]
  rw [periodic_sum_full_blocks hp,← sum_zmod_eq_sum_range]

theorem stdAddChar_residueReduction (d q : ℕ) [NeZero d] [NeZero q] (a : ZMod (d*q)) :
    ZMod.stdAddChar ((d : ZMod (d*q))*a)=ZMod.stdAddChar (residueReduction d q a) := by
  have hh := stdAddChar_mul_modulus_left d q (a.val : ℤ)
  simpa only [Int.cast_natCast,ZMod.natCast_zmod_val,residueReduction_eq_val] using hh

theorem productCompleteSum_multiple (d q k L : ℕ) [NeZero d] [NeZero q] (a : ZMod (d*q)) :
    productCompleteSum (d*q) k L ((d : ZMod (d*q))*a)=
      (d : ℂ)^L*productCompleteSum q k L (residueReduction d q a) := by
  induction L generalizing a with
  | zero => simp only [productCompleteSum_zero,pow_zero,one_mul]; exact stdAddChar_residueReduction d q a
  | succ L ih =>
      rw [productCompleteSum_succ]
      simp_rw [mul_assoc,ih,map_mul,map_pow]
      rw [← Finset.mul_sum,
        sum_residueReduction d q (fun x=>productCompleteSum q k L (residueReduction d q a*x^k)),
        ← productCompleteSum_succ,pow_succ]
      ring

theorem productCompleteMean_multiple (d q k L : ℕ) [NeZero d] [NeZero q] (a : ZMod (d*q)) :
    productCompleteMean (d*q) k L ((d : ZMod (d*q))*a)=
      productCompleteMean q k L (residueReduction d q a) := by
  rw [productCompleteMean,productCompleteSum_multiple,Nat.cast_mul,mul_pow]
  have hd : (d : ℂ)^L≠0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne d)
  rw [mul_div_mul_left _ _ hd]
  rfl

theorem ordinaryCompleteMean_multiple (d q k : ℕ) [NeZero d] [NeZero q] (a : ZMod (d*q)) :
    ordinaryCompleteMean (d*q) k ((d : ZMod (d*q))*a)=
      ordinaryCompleteMean q k (residueReduction d q a) := by
  simpa only [productCompleteMean,productCompleteSum_one,pow_one,ordinaryCompleteMean] using
    productCompleteMean_multiple d q k 1 a

theorem productSingularTerm_multiple (d q k u v L : ℕ) [NeZero d] [NeZero q]
    (n : ℤ) (a : ZMod (d*q)) :
    productSingularTerm (d*q) k u v L n ((d : ZMod (d*q))*a)=
      productSingularTerm q k u v L n (residueReduction d q a) := by
  unfold productSingularTerm
  rw [ordinaryCompleteMean_multiple,productCompleteMean_multiple]
  have hh : -((d : ZMod (d*q))*a)*(n : ZMod (d*q))=(d : ZMod (d*q))*(-a*(n : ZMod (d*q))) := by ring
  rw [hh,stdAddChar_residueReduction,map_mul,map_neg,map_intCast]

#print axioms productSingularTerm_multiple
end Waring.EndgameCompletion
