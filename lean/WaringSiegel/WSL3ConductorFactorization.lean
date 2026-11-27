import WaringSiegel.WSL3ConductorIdealSeries

/-! # WSL3: exact prime-exponent coordinates on nonzero integral ideals -/
noncomputable section
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

@[simp] theorem idealPrimeExponent_one
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    idealPrimeExponent (1 : Ideal (𝓞 K)) v = 0 := by
  simp only [idealPrimeExponent, Associates.mk_one, Associates.factors_one,
    Associates.count_zero v.associates_irreducible]

theorem idealPrimeExponent_mul (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    idealPrimeExponent (I*J) v = idealPrimeExponent I v + idealPrimeExponent J v := by
  exact Associates.count_mul
    (Associates.mk_ne_zero.mpr hI) (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible

theorem idealPrimeExponent_prime_pow
    (v w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    idealPrimeExponent (w.asIdeal^e) v = if v = w then e else 0 := by
  unfold idealPrimeExponent
  rw [Associates.mk_pow, Associates.count_pow
    (Associates.mk_ne_zero.mpr w.ne_bot) v.associates_irreducible]
  by_cases h : v = w
  · subst w
    rw [if_pos rfl, Associates.count_self v.associates_irreducible, mul_one]
  · have ha : Associates.mk v.asIdeal ≠ Associates.mk w.asIdeal := by
      intro he
      apply h
      apply IsDedekindDomain.HeightOneSpectrum.ext
      exact associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp he)
    rw [if_neg h, Associates.count_eq_zero_of_ne v.associates_irreducible
      w.associates_irreducible ha, mul_zero]

theorem idealPrimeExponent_finset_prod
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    idealPrimeExponent (∏ w ∈ S, w.asIdeal^e w) v = if v ∈ S then e v else 0 := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, idealPrimeExponent_one, Finset.notMem_empty, if_false]
  | @insert w S hw ih =>
    rw [Finset.prod_insert hw, idealPrimeExponent_mul _ _ (pow_ne_zero _ w.ne_bot)
      (prime_power_product_ne_zero S e), idealPrimeExponent_prime_pow, ih]
    by_cases hv : v = w
    · subst v
      simp only [if_pos rfl, hw, if_false, add_zero, Finset.mem_insert_self, if_true]
    · simp only [hv, if_false, zero_add, Finset.mem_insert, false_or]

theorem idealPrimeSupport_finset_prod
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ)
    (he : ∀ v ∈ S, 0 < e v) :
    idealPrimeSupport (∏ v ∈ S, v.asIdeal^e v) (prime_power_product_ne_zero S e) = S := by
  ext v
  change v ∈ (Ideal.finite_factors (prime_power_product_ne_zero S e)).toFinset ↔ v ∈ S
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    ← Associates.count_ne_zero_iff_dvd (prime_power_product_ne_zero S e) v.irreducible]
  change idealPrimeExponent (∏ w ∈ S, w.asIdeal^e w) v ≠ 0 ↔ v ∈ S
  rw [idealPrimeExponent_finset_prod]
  by_cases hv : v ∈ S
  · simp only [hv, if_true, iff_true]
    exact (he v hv).ne'
  · simp only [hv, if_false, ne_eq, not_true, iff_self]

end WaringSiegel
