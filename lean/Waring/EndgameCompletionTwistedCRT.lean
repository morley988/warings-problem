import Waring.EndgameCompletionTwistedStationary
import Waring.EndgameCompletionCRT
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Composite twisted complete sums

The elementary exponent-three-quarters bound is assembled over coprime
prime powers.  The coefficient of the linear twist remains unchanged in
the CRT parameterization, so its gcd factors multiply exactly.
-/

noncomputable section
open scoped BigOperators Classical

namespace Waring.EndgameCompletion

theorem twistedMonomialSumMod_coprime_phase (q r k : ℕ)
    [NeZero q] [NeZero r] (hk : 0<k) (a b : ℤ) (x : ZMod q × ZMod r) :
    ZMod.stdAddChar ((a : ZMod (q*r))*(coprimeResidueLift q r x)^k+
        (b : ZMod (q*r))*coprimeResidueLift q r x) =
      ZMod.stdAddChar (((a*(r : ℤ)^(k-1) : ℤ) : ZMod q)*x.1^k+(b : ZMod q)*x.1)*
      ZMod.stdAddChar (((a*(q : ℤ)^(k-1) : ℤ) : ZMod r)*x.2^k+(b : ZMod r)*x.2) := by
  have hlinear : ZMod.stdAddChar ((b : ZMod (q*r))*coprimeResidueLift q r x)=
      ZMod.stdAddChar ((b : ZMod q)*x.1)*ZMod.stdAddChar ((b : ZMod r)*x.2) := by
    simpa only [pow_one,Nat.sub_self,pow_zero,mul_one] using
      completeMonomialSumMod_coprime_phase q r 1 (by norm_num) b x
  rw [AddChar.map_add_eq_mul,completeMonomialSumMod_coprime_phase q r k hk a,
    hlinear,AddChar.map_add_eq_mul,AddChar.map_add_eq_mul]
  ring

theorem twistedMonomialSumMod_coprime (q r k : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (hk : 0<k) (a b : ℤ) :
    twistedMonomialSumMod (q*r) k (a : ZMod (q*r)) (b : ZMod (q*r)) =
      twistedMonomialSumMod q k ((a*(r : ℤ)^(k-1) : ℤ) : ZMod q) (b : ZMod q)*
      twistedMonomialSumMod r k ((a*(q : ℤ)^(k-1) : ℤ) : ZMod r) (b : ZMod r) := by
  unfold twistedMonomialSumMod
  rw [← (coprimeResidueLift_bijective q r hqr).sum_comp]
  simp_rw [twistedMonomialSumMod_coprime_phase q r k hk a b]
  rw [Fintype.sum_prod_type,Finset.sum_mul_sum]

theorem twistedMonomialSumMod_coprime_nat (q r k a b : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (hk : 0<k) :
    twistedMonomialSumMod (q*r) k (a : ZMod (q*r)) (b : ZMod (q*r)) =
      twistedMonomialSumMod q k ((a*r^(k-1) : ℕ) : ZMod q) (b : ZMod q)*
      twistedMonomialSumMod r k ((a*q^(k-1) : ℕ) : ZMod r) (b : ZMod r) := by
  simpa only [Int.cast_natCast,Int.cast_mul,Int.cast_pow,Nat.cast_mul,Nat.cast_pow] using
    twistedMonomialSumMod_coprime q r k hqr hk (a : ℤ) (b : ℤ)

theorem twistedMonomialSumMod_one (k a b : ℕ) :
    twistedMonomialSumMod 1 k (a : ZMod 1) (b : ZMod 1)=1 := by
  unfold twistedMonomialSumMod
  have hh (x : ZMod 1) : (a : ZMod 1)*x^k+(b : ZMod 1)*x=0 := Subsingleton.elim _ _
  simp [hh,AddChar.map_zero_eq_one]

/-- Every distinct prime contributes just one fixed degree-dependent
constant. This bound retains the gcd of the linear coefficient exactly. -/
theorem twistedMonomialSumMod_fourth_omega_le (k : ℕ) (hk : 2≤k)
    (q : ℕ) [NeZero q] (a b : ℕ) (ha : Nat.Coprime a q) :
    ‖twistedMonomialSumMod q k (a : ZMod q) (b : ZMod q)‖^4 ≤
      ((2*k^2 : ℕ) : ℝ)^(4*q.primeFactors.card)*(q : ℝ)^3*(Nat.gcd b q : ℝ)^4 := by
  suffices H : ∀ q (hq : q≠0), letI : NeZero q := ⟨hq⟩
      ∀ a b : ℕ, Nat.Coprime a q →
      ‖twistedMonomialSumMod q k (a : ZMod q) (b : ZMod q)‖^4 ≤
        ((2*k^2 : ℕ) : ℝ)^(4*q.primeFactors.card)*(q : ℝ)^3*(Nat.gcd b q : ℝ)^4 by
    exact H q (NeZero.ne q) a b ha
  intro q
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p l hp hl =>
      intro hq
      letI : Fact p.Prime := ⟨hp⟩
      letI : NeZero (p^l) := ⟨hq⟩
      intro a b ha
      let u := (ZMod.isUnit_iff_coprime a (p^l)).mpr ha
      have h := twistedMonomialSumMod_primepower_fourth_uniform l k (by omega) hk
        u.unit (b : ZMod (p^l))
      have hgc : Nat.gcd ((b : ZMod (p^l)).val) (p^l)=Nat.gcd b (p^l) := by
        rw [ZMod.val_natCast,← Nat.gcd_rec,Nat.gcd_comm]
      simpa only [IsUnit.unit_spec,hgc,Nat.primeFactors_pow p hl.ne',hp.primeFactors,
        Finset.card_singleton,Nat.mul_one] using h
  | zero => intro hq; exact False.elim (hq rfl)
  | one => intro hq; simp [twistedMonomialSumMod_one]
  | coprime q r hq hr hqr ihq ihr =>
      intro hqr0
      letI : NeZero q := ⟨by omega⟩
      letI : NeZero r := ⟨by omega⟩
      letI : NeZero (q*r) := ⟨hqr0⟩
      intro a b ha
      have haq : Nat.Coprime (a*r^(k-1)) q :=
        (ha.of_dvd_right (dvd_mul_right q r)).mul_left (hqr.symm.pow_left _)
      have har : Nat.Coprime (a*q^(k-1)) r :=
        (ha.of_dvd_right (dvd_mul_left r q)).mul_left (hqr.pow_left _)
      have Hq := ihq (NeZero.ne q) (a*r^(k-1)) b haq
      have Hr := ihr (NeZero.ne r) (a*q^(k-1)) b har
      rw [twistedMonomialSumMod_coprime_nat q r k a b hqr (by omega),norm_mul,mul_pow]
      apply (mul_le_mul Hq Hr (by positivity) (by positivity)).trans_eq
      have hcard : (q*r).primeFactors.card=q.primeFactors.card+r.primeFactors.card := by
        rw [hqr.primeFactors_mul,Finset.card_union_of_disjoint hqr.disjoint_primeFactors]
      rw [hcard,Nat.mul_add,pow_add,hqr.gcd_mul b]
      simp only [Nat.cast_mul,mul_pow]
      ring

theorem norm_twistedMonomialSumMod_omega_le (k : ℕ) (hk : 2≤k)
    (q : ℕ) [NeZero q] (a b : ℕ) (ha : Nat.Coprime a q) :
    ‖twistedMonomialSumMod q k (a : ZMod q) (b : ZMod q)‖ ≤
      ((2*k^2 : ℕ) : ℝ)^q.primeFactors.card*(q : ℝ)^(3/4 : ℝ)*Nat.gcd b q := by
  have hq0 : (0 : ℝ)≤q := Nat.cast_nonneg _
  have hpow : ((q : ℝ)^(3/4 : ℝ))^4=(q : ℝ)^3 := by
    rw [← Real.rpow_mul_natCast hq0]
    norm_num
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : 4≠0)).mp
  calc
    _ ≤ ((2*k^2 : ℕ) : ℝ)^(4*q.primeFactors.card)*(q : ℝ)^3*(Nat.gcd b q : ℝ)^4 :=
      twistedMonomialSumMod_fourth_omega_le k hk q a b ha
    _ = _ := by
      rw [mul_pow,mul_pow,hpow,← pow_mul]
      simp only [Nat.mul_comm]

theorem norm_twistedMonomialSumMod_divisor_le (k : ℕ) (hk : 2≤k)
    (q : ℕ) [NeZero q] (a b : ℕ) (ha : Nat.Coprime a q) :
    ‖twistedMonomialSumMod q k (a : ZMod q) (b : ZMod q)‖ ≤
      (q.divisors.card : ℝ)^(2*k^2)*(q : ℝ)^(3/4 : ℝ)*Nat.gcd b q := by
  have hc : (2*k^2)^q.primeFactors.card ≤ q.divisors.card^(2*k^2) := by
    calc
      _ ≤ (2^(2*k^2))^q.primeFactors.card := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = (2^q.primeFactors.card)^(2*k^2) := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_left (PolicyCompletionRoots.two_pow_primeFactors_card_le_divisors
        (Nat.pos_of_ne_zero (NeZero.ne q))) _
  apply (norm_twistedMonomialSumMod_omega_le k hk q a b ha).trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact_mod_cast hc

/-- The actual elementary composite estimate needed for Fourier completion.
Every singular prime and nonunit linear twist is included. -/
theorem norm_twistedMonomialSumMod_le_rpow (k : ℕ) (hk : 2≤k)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) [NeZero q] (a b : ℕ), Nat.Coprime a q →
      ‖twistedMonomialSumMod q k (a : ZMod q) (b : ZMod q)‖ ≤
        C*(q : ℝ)^(3/4+ε : ℝ)*Nat.gcd b q := by
  obtain ⟨C,hC,hdiv⟩ := AuxiliaryL2Grouping.divisor_power_le_rpow (2*k^2) hε
  refine ⟨C,hC,?_⟩
  intro q _ a b ha
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  calc
    _ ≤ (q.divisors.card : ℝ)^(2*k^2)*(q : ℝ)^(3/4 : ℝ)*Nat.gcd b q :=
      norm_twistedMonomialSumMod_divisor_le k hk q a b ha
    _ ≤ (C*(q : ℝ)^ε)*(q : ℝ)^(3/4 : ℝ)*Nat.gcd b q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hdiv q hq)
        (by positivity)) (by positivity)
    _ = _ := by
      rw [Real.rpow_add (by exact_mod_cast hq : (0 : ℝ)<q)]
      ring

#print axioms twistedMonomialSumMod_coprime
#print axioms twistedMonomialSumMod_fourth_omega_le
#print axioms norm_twistedMonomialSumMod_le_rpow

end Waring.EndgameCompletion
