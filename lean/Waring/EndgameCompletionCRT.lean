import Waring.EndgameCompletionPrimePowers

/-!
# Chinese-remainder factorization of complete monomial sums

The product-modulus sum is reindexed by the explicit bijection
`(u,v) ↦ r*u+q*v`.  This keeps the phase calculation elementary and
records the coefficient twists needed for later primitive moments.
-/

noncomputable section

open scoped BigOperators

namespace Waring.EndgameCompletion

theorem add_pow_of_mul_zero {R : Type*} [CommRing R] (x y : R)
    (hxy : x*y=0) (k : ℕ) (hk : 0 < k) :
    (x+y)^k=x^k+y^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k=0
    · subst k
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hx : x^k*y=0 := by
        obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        rw [pow_succ, mul_assoc, hxy, mul_zero]
      have hy : y^k*x=0 := by
        obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        rw [pow_succ, mul_assoc, mul_comm y x, hxy, mul_zero]
      rw [pow_succ, ih hkpos, add_mul, mul_add, mul_add, hx, hy,
        add_zero, zero_add, ← pow_succ, ← pow_succ]

def coprimeResidueLift (q r : ℕ) (x : ZMod q × ZMod r) : ZMod (q*r) :=
  (r : ZMod (q*r))*(x.1.val : ZMod (q*r))+
    (q : ZMod (q*r))*(x.2.val : ZMod (q*r))

theorem coprimeResidueLift_bijective (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) : Function.Bijective (coprimeResidueLift q r) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simp [Fintype.card_prod, ZMod.card]⟩
  intro x y hxy
  have hq : (r : ZMod q)*x.1=(r : ZMod q)*y.1 := by
    have hh := congrArg (ZMod.castHom (dvd_mul_right q r) (ZMod q)) hxy
    simpa only [coprimeResidueLift, map_add, map_mul, map_natCast,
      ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val] using hh
  have hr : (q : ZMod r)*x.2=(q : ZMod r)*y.2 := by
    have hh := congrArg (ZMod.castHom (dvd_mul_left r q) (ZMod r)) hxy
    simpa only [coprimeResidueLift, map_add, map_mul, map_natCast,
      ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_zmod_val] using hh
  exact Prod.ext (((ZMod.isUnit_iff_coprime r q).mpr hqr.symm).mul_left_cancel hq)
    (((ZMod.isUnit_iff_coprime q r).mpr hqr).mul_left_cancel hr)

theorem stdAddChar_mul_modulus (q r : ℕ) [NeZero q] [NeZero r] (b : ℤ) :
    ZMod.stdAddChar ((r : ZMod (q*r))*(b : ZMod (q*r))) =
      ZMod.stdAddChar (b : ZMod q) := by
  rw [show (r : ZMod (q*r))*(b : ZMod (q*r)) =
    (((r : ℤ)*b : ℤ) : ZMod (q*r)) by push_cast; rfl]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne r)
  push_cast
  field_simp

theorem stdAddChar_mul_modulus_left (q r : ℕ) [NeZero q] [NeZero r] (b : ℤ) :
    ZMod.stdAddChar ((q : ZMod (q*r))*(b : ZMod (q*r))) =
      ZMod.stdAddChar (b : ZMod r) := by
  rw [show (q : ZMod (q*r))*(b : ZMod (q*r)) =
    (((q : ℤ)*b : ℤ) : ZMod (q*r)) by push_cast; rfl]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  push_cast
  field_simp

theorem completeMonomialSumMod_coprime_phase (q r k : ℕ)
    [NeZero q] [NeZero r] (hk : 0 < k) (a : ℤ) (x : ZMod q × ZMod r) :
    ZMod.stdAddChar ((a : ZMod (q*r))*(coprimeResidueLift q r x)^k) =
      ZMod.stdAddChar (((a*(r : ℤ)^(k-1) : ℤ) : ZMod q)*x.1^k)*
      ZMod.stdAddChar (((a*(q : ℤ)^(k-1) : ℤ) : ZMod r)*x.2^k) := by
  have hcross : ((r : ZMod (q*r))*x.1.val)*((q : ZMod (q*r))*x.2.val)=0 := by
    calc
      _ = ((q*r : ℕ) : ZMod (q*r))*(x.1.val*x.2.val : ℕ) := by push_cast; ring
      _ = 0 := by simp
  rw [coprimeResidueLift, add_pow_of_mul_zero _ _ hcross k hk, mul_add,
    AddChar.map_add_eq_mul]
  congr 1
  · calc
      _ = ZMod.stdAddChar ((r : ZMod (q*r))*
          ((a*(r : ℤ)^(k-1)*(x.1.val : ℤ)^k : ℤ) : ZMod (q*r))) := by
        congr 1
        push_cast
        rw [mul_pow, show (r : ZMod (q*r))^k =
          (r : ZMod (q*r))^(k-1)*(r : ZMod (q*r)) by
          rw [← pow_succ, Nat.sub_add_cancel hk]]
        ring
      _ = _ := by
        rw [stdAddChar_mul_modulus]
        push_cast
        rw [ZMod.natCast_zmod_val]
  · calc
      _ = ZMod.stdAddChar ((q : ZMod (q*r))*
          ((a*(q : ℤ)^(k-1)*(x.2.val : ℤ)^k : ℤ) : ZMod (q*r))) := by
        congr 1
        push_cast
        rw [mul_pow, show (q : ZMod (q*r))^k =
          (q : ZMod (q*r))^(k-1)*(q : ZMod (q*r)) by
          rw [← pow_succ, Nat.sub_add_cancel hk]]
        ring
      _ = _ := by
        rw [stdAddChar_mul_modulus_left]
        push_cast
        rw [ZMod.natCast_zmod_val]

/-- Exact complete-sum multiplicativity, including the coefficient twists. -/
theorem completeMonomialSumMod_coprime (q r k : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (hk : 0 < k) (a : ℤ) :
    completeMonomialSumMod (q*r) k (a : ZMod (q*r)) =
      completeMonomialSumMod q k ((a*(r : ℤ)^(k-1) : ℤ) : ZMod q)*
      completeMonomialSumMod r k ((a*(q : ℤ)^(k-1) : ℤ) : ZMod r) := by
  unfold completeMonomialSumMod
  rw [← (coprimeResidueLift_bijective q r hqr).sum_comp]
  simp_rw [completeMonomialSumMod_coprime_phase q r k hk a]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem completeMonomialSum_coprime (q r k : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (hk : 0 < k) (a : ℤ) :
    completeMonomialSum k a (q*r) =
      completeMonomialSum k (a*(r : ℤ)^(k-1)) q*
      completeMonomialSum k (a*(q : ℤ)^(k-1)) r := by
  simp only [completeMonomialSum_eq_mod]
  exact completeMonomialSumMod_coprime q r k hqr hk a

#print axioms completeMonomialSumMod_coprime
#print axioms completeMonomialSum_coprime

end Waring.EndgameCompletion
