import Waring.EndgameCompletionCRT

/-!
# Primitive complete-sum moments

These nonnegative coefficients are the arithmetic factors in ordinary
major-arc moments.  Chinese remainder factorization is proved for the
actual coefficients, with the unit twists removed by exact permutation.
-/

noncomputable section

open scoped BigOperators

namespace Waring.EndgameCompletion

def normalizedCompleteSum (q : ℕ) [NeZero q] (k : ℕ) (a : ZMod q) : ℝ :=
  ‖completeMonomialSumMod q k a‖/(q : ℝ)

def primitiveCompleteMoment (q : ℕ) [NeZero q] (k s : ℕ) : ℝ :=
  ∑ a : (ZMod q)ˣ, (normalizedCompleteSum q k a)^s

theorem norm_completeMonomialSumMod_le (q : ℕ) [NeZero q] (k : ℕ) (a : ZMod q) :
    ‖completeMonomialSumMod q k a‖ ≤ q := by
  unfold completeMonomialSumMod
  calc
    _ ≤ ∑ x : ZMod q, ‖ZMod.stdAddChar (a*x^k)‖ := norm_sum_le _ _
    _ = _ := by simp [ZMod.stdAddChar_apply, ZMod.card]

theorem normalizedCompleteSum_nonneg (q : ℕ) [NeZero q] (k : ℕ) (a : ZMod q) :
    0 ≤ normalizedCompleteSum q k a := div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)

theorem normalizedCompleteSum_le_one (q : ℕ) [NeZero q] (k : ℕ) (a : ZMod q) :
    normalizedCompleteSum q k a ≤ 1 := by
  apply (div_le_one (by exact_mod_cast NeZero.pos q : (0 : ℝ) < q)).mpr
  exact norm_completeMonomialSumMod_le q k a

theorem primitiveCompleteMoment_nonneg (q : ℕ) [NeZero q] (k s : ℕ) :
    0 ≤ primitiveCompleteMoment q k s :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg (normalizedCompleteSum_nonneg ..) _)

def coprimeUnitsEquiv (q r : ℕ) (hqr : q.Coprime r) :
    (ZMod (q*r))ˣ ≃ (ZMod q)ˣ × (ZMod r)ˣ :=
  ((Units.mapEquiv (ZMod.chineseRemainder hqr).toMulEquiv).trans
    MulEquiv.prodUnits).toEquiv

theorem coprimeUnitsEquiv_fst (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (a : (ZMod (q*r))ˣ) :
    ((coprimeUnitsEquiv q r hqr a).1 : ZMod q) = ((a : ZMod (q*r)).val : ZMod q) := by
  change (ZMod.cast (a : ZMod (q*r)) : ZMod q × ZMod r).1 = _
  rw [Prod.fst_zmod_cast, ZMod.cast_eq_val]

theorem coprimeUnitsEquiv_snd (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (a : (ZMod (q*r))ˣ) :
    ((coprimeUnitsEquiv q r hqr a).2 : ZMod r) = ((a : ZMod (q*r)).val : ZMod r) := by
  change (ZMod.cast (a : ZMod (q*r)) : ZMod q × ZMod r).2 = _
  rw [Prod.snd_zmod_cast, ZMod.cast_eq_val]

theorem completeMonomialSumMod_coprime_units (q r k : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (hk : 0 < k) (a : (ZMod (q*r))ˣ) :
    completeMonomialSumMod (q*r) k a =
      completeMonomialSumMod q k
        ((coprimeUnitsEquiv q r hqr a).1*(ZMod.unitOfCoprime r hqr.symm)^(k-1)) *
      completeMonomialSumMod r k
        ((coprimeUnitsEquiv q r hqr a).2*(ZMod.unitOfCoprime q hqr)^(k-1)) := by
  have hh := completeMonomialSumMod_coprime q r k hqr hk ((a : ZMod (q*r)).val : ℤ)
  simpa only [Int.cast_natCast, Int.cast_mul, Int.cast_pow, ZMod.natCast_zmod_val,
    Units.val_mul, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
    coprimeUnitsEquiv_fst, coprimeUnitsEquiv_snd] using hh

theorem normalizedCompleteSum_coprime_units (q r k : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (hk : 0 < k) (a : (ZMod (q*r))ˣ) :
    normalizedCompleteSum (q*r) k a =
      normalizedCompleteSum q k
        ((coprimeUnitsEquiv q r hqr a).1*(ZMod.unitOfCoprime r hqr.symm)^(k-1)) *
      normalizedCompleteSum r k
        ((coprimeUnitsEquiv q r hqr a).2*(ZMod.unitOfCoprime q hqr)^(k-1)) := by
  unfold normalizedCompleteSum
  rw [completeMonomialSumMod_coprime_units q r k hqr hk a, norm_mul,
    Nat.cast_mul, mul_div_mul_comm]

theorem sum_units_mul_right {M : Type*} [Monoid M] [Fintype Mˣ]
    (c : Mˣ) (w : Mˣ → ℝ) : (∑ a : Mˣ, w (a*c)) = ∑ a : Mˣ, w a := by
  exact Fintype.sum_equiv (Equiv.mulRight c) _ _ (fun _ => rfl)

/-- The actual normalized primitive coefficients are multiplicative on
coprime positive moduli. -/
theorem primitiveCompleteMoment_coprime (q r k s : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (hk : 0 < k) :
    primitiveCompleteMoment (q*r) k s =
      primitiveCompleteMoment q k s*primitiveCompleteMoment r k s := by
  unfold primitiveCompleteMoment
  simp_rw [normalizedCompleteSum_coprime_units q r k hqr hk, mul_pow]
  calc
    _ = ∑ x : (ZMod q)ˣ × (ZMod r)ˣ,
      normalizedCompleteSum q k (x.1*(ZMod.unitOfCoprime r hqr.symm)^(k-1))^s *
      normalizedCompleteSum r k (x.2*(ZMod.unitOfCoprime q hqr)^(k-1))^s := by
      apply Fintype.sum_equiv (coprimeUnitsEquiv q r hqr)
      intro a
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      dsimp only
      rw [← Fintype.sum_mul_sum]
      exact congrArg₂ (fun x y : ℝ => x*y)
        (sum_units_mul_right ((ZMod.unitOfCoprime r hqr.symm)^(k-1))
          (fun a : (ZMod q)ˣ => (normalizedCompleteSum q k a)^s))
        (sum_units_mul_right ((ZMod.unitOfCoprime q hqr)^(k-1))
          (fun a : (ZMod r)ˣ => (normalizedCompleteSum r k a)^s))

theorem primitiveCompleteMoment_le_of_uniform (q k s : ℕ) [NeZero q]
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a : (ZMod q)ˣ, (normalizedCompleteSum q k a)^s ≤ C) :
    primitiveCompleteMoment q k s ≤ q*C := by
  have hcard : Fintype.card (ZMod q)ˣ ≤ q := by
    simpa only [ZMod.card] using
      Fintype.card_le_of_injective (fun a : (ZMod q)ˣ => a.val) Units.val_injective
  calc
    _ ≤ ∑ _a : (ZMod q)ˣ, C := Finset.sum_le_sum (fun a _ => hbound a)
    _ = (Fintype.card (ZMod q)ˣ : ℝ)*C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC

theorem normalizedCompleteSum_prime_sq_le {p : ℕ} [Fact p.Prime]
    (k : ℕ) (hk : 0 < k) (a : (ZMod p)ˣ) :
    (normalizedCompleteSum p k a)^2 ≤ 2*(k : ℝ)^2/p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hb := completeMonomialSumMod_prime_sq_le k hk a.ne_zero
  unfold normalizedCompleteSum
  rw [div_pow]
  apply (div_le_div_iff₀ (pow_pos hp 2) hp).mpr
  nlinarith [mul_le_mul_of_nonneg_right hb hp.le]

/-- A uniform `p⁻²` majorant for every prime coefficient moment of order
at least six. It follows from the proved second-power prime estimate and
the trivial normalized bound by one. -/
theorem primitiveCompleteMoment_prime_le {p : ℕ} [Fact p.Prime]
    (k s : ℕ) (hk : 0 < k) (hs : 6 ≤ s) :
    primitiveCompleteMoment p k s ≤ 8*(k : ℝ)^6/(p : ℝ)^2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hb : primitiveCompleteMoment p k s ≤
      (p : ℝ)*(2*(k : ℝ)^2/(p : ℝ))^3 := by
    apply primitiveCompleteMoment_le_of_uniform p k s (by positivity)
    intro a
    calc
      _ ≤ (normalizedCompleteSum p k a)^6 :=
        pow_le_pow_of_le_one (normalizedCompleteSum_nonneg ..)
          (normalizedCompleteSum_le_one ..) hs
      _ = ((normalizedCompleteSum p k a)^2)^3 := by ring
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) (normalizedCompleteSum_prime_sq_le k hk a) 3
  convert hb using 1
  field_simp
  ring

theorem prime_not_dvd_unit_val {p : ℕ} [Fact p.Prime]
    (l : ℕ) (hl : 0 < l) (a : (ZMod (p^l))ˣ) : ¬ p ∣ (a : ZMod (p^l)).val := by
  intro ha
  have hdiv := Nat.dvd_gcd ha (dvd_pow_self p (Nat.ne_of_gt hl))
  rw [(ZMod.val_coe_unit_coprime a)] at hdiv
  exact (Fact.out : p.Prime).not_dvd_one hdiv

theorem normalizedCompleteSum_primepower_small {p : ℕ} [Fact p.Prime]
    (l k : ℕ) (hl : 2 ≤ l) (hlk : l ≤ k) (a : (ZMod (p^l))ˣ)
    (hpk : ¬ p ∣ k) :
    normalizedCompleteSum (p^l) k a = 1/(p : ℝ) := by
  unfold normalizedCompleteSum
  rw [completeMonomialSumMod_primepower_small l k hl hlk a
    (prime_not_dvd_unit_val l (by omega) a) hpk, Complex.norm_natCast]
  push_cast
  rw [show (p : ℝ)^l=(p : ℝ)^(l-1)*p by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ l)]]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

theorem primitiveCompleteMoment_primepower_small_le {p : ℕ} [Fact p.Prime]
    (l k s : ℕ) (hl : 2 ≤ l) (hlk : l ≤ k) (hpk : ¬ p ∣ k) :
    primitiveCompleteMoment (p^l) k s ≤ (p : ℝ)^l/(p : ℝ)^s := by
  have hh := primitiveCompleteMoment_le_of_uniform (p^l) k s
    (C := (1/(p : ℝ))^s) (by positivity)
    (fun a => le_of_eq (congrArg (fun x : ℝ => x^s)
      (normalizedCompleteSum_primepower_small l k hl hlk a hpk)))
  simpa only [Nat.cast_pow, div_pow, one_pow, mul_one_div] using hh

#print axioms primitiveCompleteMoment_coprime
#print axioms primitiveCompleteMoment_prime_le
#print axioms primitiveCompleteMoment_primepower_small_le

end Waring.EndgameCompletion
