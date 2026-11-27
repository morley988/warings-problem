import Waring.PolicyCompletionPolynomialGcd

/-! # Exact CRT factorization for general complete polynomial sums -/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionPolynomialCRT
open Polynomial EndgameCompletion PolicyCompletionPolynomialResidues
  PolicyCompletionPolynomialGcd PolicyCompletionPolynomialPrimePower
  PolicyCompletionPolynomialHuaBounds

theorem stdAddChar_bezout (q r : ℕ) [NeZero q] [NeZero r]
    (u v : ℤ) (hbez : (r : ℤ)*u+(q : ℤ)*v=1) (b : ℤ) :
    ZMod.stdAddChar (b : ZMod (q*r))=
      ZMod.stdAddChar ((u*b : ℤ) : ZMod q)*ZMod.stdAddChar ((v*b : ℤ) : ZMod r) := by
  have he : (b : ZMod (q*r))=
      (r : ZMod (q*r))*((u*b : ℤ) : ZMod (q*r))+
        (q : ZMod (q*r))*((v*b : ℤ) : ZMod (q*r)) := by
    have hi : b=(r : ℤ)*(u*b)+(q : ℤ)*(v*b) := by nlinarith [congrArg (fun z : ℤ => z*b) hbez]
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ZMod (q*r))) hi
  rw [he,AddChar.map_add_eq_mul,stdAddChar_mul_modulus,stdAddChar_mul_modulus_left]

theorem chineseRemainder_fst_val (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (x : ZMod (q*r)) :
    (ZMod.chineseRemainder hqr x).1=(x.val : ZMod q) := by
  nth_rw 1 [← ZMod.natCast_zmod_val x]
  rw [map_natCast]
  rfl

theorem chineseRemainder_snd_val (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (x : ZMod (q*r)) :
    (ZMod.chineseRemainder hqr x).2=(x.val : ZMod r) := by
  nth_rw 1 [← ZMod.natCast_zmod_val x]
  rw [map_natCast]
  rfl

theorem integerPolynomialSum_crt (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (u v : ℤ) (hbez : (r : ℤ)*u+(q : ℤ)*v=1)
    (f : Polynomial ℤ) :
    integerPolynomialSum (q*r) f=
      integerPolynomialSum q (C u*f)*integerPolynomialSum r (C v*f) := by
  have hphase (x : ZMod (q*r)) :
      ZMod.stdAddChar ((f.map (Int.castRingHom (ZMod (q*r)))).eval x)=
        ZMod.stdAddChar (((C u*f).map (Int.castRingHom (ZMod q))).eval
          (ZMod.chineseRemainder hqr x).1)*
        ZMod.stdAddChar (((C v*f).map (Int.castRingHom (ZMod r))).eval
          (ZMod.chineseRemainder hqr x).2) := by
    rw [chineseRemainder_fst_val,chineseRemainder_snd_val]
    have he : (f.map (Int.castRingHom (ZMod (q*r)))).eval x=
        ((f.eval (x.val : ℤ) : ℤ) : ZMod (q*r)) := by
      nth_rw 1 [← ZMod.natCast_zmod_val x]
      rw [Polynomial.eval_natCast_map]
      rfl
    rw [he,Polynomial.eval_natCast_map,Polynomial.eval_natCast_map,
      Polynomial.eval_mul,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_C]
    exact stdAddChar_bezout q r u v hbez _
  unfold integerPolynomialSum PolicyCompletionPolynomialStationary.completePolynomialSum
  calc
    _ = ∑ z : ZMod q × ZMod r,
        ZMod.stdAddChar (((C u*f).map (Int.castRingHom (ZMod q))).eval z.1)*
        ZMod.stdAddChar (((C v*f).map (Int.castRingHom (ZMod r))).eval z.2) :=
      Fintype.sum_equiv (ZMod.chineseRemainder hqr).toEquiv _ _ hphase
    _ = _ := by rw [Fintype.sum_prod_type,Finset.sum_mul_sum]

theorem exists_bezout_twists (q r : ℕ) (hqr : q.Coprime r) :
    ∃ u v : ℤ,(r : ℤ)*u+(q : ℤ)*v=1 ∧
      IsCoprime (q : ℤ) u ∧ IsCoprime (r : ℤ) v := by
  let u := Nat.gcdB q r
  let v := Nat.gcdA q r
  have he : (r : ℤ)*u+(q : ℤ)*v=1 := by
    have hh := Nat.gcd_eq_gcd_ab q r
    rw [hqr.gcd_eq_one,Nat.cast_one] at hh
    dsimp [u,v]
    linarith
  refine ⟨u,v,he,?_,?_⟩
  · exact ⟨v,(r : ℤ),by nlinarith⟩
  · exact ⟨u,(q : ℤ),by nlinarith⟩

/-- Each prime contributes one degree constant. Coprime factorization
retains the exact gcd of the nonconstant coefficient divisor bound. -/
theorem polynomial_sum_omega_bound (D : ℕ) (hD : 1 ≤ D)
    (q : ℕ) [NeZero q] (f : Polynomial ℤ) (hfD : f.natDegree ≤ D)
    (B : ℕ) (hB : CoefficientDivisorBoundAt q f B) :
    ‖integerPolynomialSum q f‖ ≤
      (completeSumConstant D)^q.primeFactors.card*(q : ℝ)^(1-1/(D : ℝ))*
        (Nat.gcd q B : ℝ)^(1/(D : ℝ)) := by
  have hCpos := completeSumConstant_pos hD
  suffices H : ∀ q (hq : q≠0),letI : NeZero q := ⟨hq⟩
      ∀ (f : Polynomial ℤ),f.natDegree ≤ D → ∀ B : ℕ,CoefficientDivisorBoundAt q f B →
      ‖integerPolynomialSum q f‖ ≤
        (completeSumConstant D)^q.primeFactors.card*(q : ℝ)^(1-1/(D : ℝ))*
          (Nat.gcd q B : ℝ)^(1/(D : ℝ)) by
    exact H q (NeZero.ne q) f hfD B hB
  intro q
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => intro hq; exact False.elim (hq rfl)
  | one =>
      intro hq f hfD B hB
      simpa using norm_integerPolynomialSum_le 1 f
  | prime_pow p l hp hl =>
      intro hq
      letI : Fact p.Prime := ⟨hp⟩
      letI : NeZero (p^l) := ⟨hq⟩
      intro f hfD B hB
      simpa only [Nat.primeFactors_pow p hl.ne',hp.primeFactors,Finset.card_singleton,pow_one] using
        polynomial_primepower_gcd_bound hD l f hfD B hB
  | coprime q r hq hr hqr ihq ihr =>
      intro hqr0
      letI : NeZero q := ⟨by omega⟩
      letI : NeZero r := ⟨by omega⟩
      letI : NeZero (q*r) := ⟨hqr0⟩
      intro f hfD B hB
      obtain ⟨u,v,hbez,hu,hv⟩ := exists_bezout_twists q r hqr
      have hqB := coefficientDivisorBoundAt_unit_mul
        (coefficientDivisorBoundAt_of_dvd hB (dvd_mul_right q r)) hu
      have hrB := coefficientDivisorBoundAt_unit_mul
        (coefficientDivisorBoundAt_of_dvd hB (dvd_mul_left r q)) hv
      have huD : (C u*f).natDegree ≤ D := (Polynomial.natDegree_C_mul_le _ _).trans hfD
      have hvD : (C v*f).natDegree ≤ D := (Polynomial.natDegree_C_mul_le _ _).trans hfD
      have Hq := ihq (NeZero.ne q) (C u*f) huD B hqB
      have Hr := ihr (NeZero.ne r) (C v*f) hvD B hrB
      rw [integerPolynomialSum_crt q r hqr u v hbez f,norm_mul]
      apply (mul_le_mul Hq Hr (by positivity) (by positivity)).trans_eq
      have hcard : (q*r).primeFactors.card=q.primeFactors.card+r.primeFactors.card := by
        rw [hqr.primeFactors_mul,Finset.card_union_of_disjoint hqr.disjoint_primeFactors]
      have hgcd : Nat.gcd (q*r) B=Nat.gcd q B*Nat.gcd r B := by
        simpa only [Nat.gcd_comm] using hqr.gcd_mul B
      rw [hcard,pow_add,hgcd]
      simp only [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      ring

#print axioms integerPolynomialSum_crt
#print axioms polynomial_sum_omega_bound
end Waring.PolicyCompletionPolynomialCRT
