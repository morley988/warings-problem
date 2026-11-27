import WaringSiegel.WSL2LocalPrimePowerQuotient
import WaringSiegel.WSL2IdealDivisors

/-!
# Cubing on units modulo arbitrary integral ideals

The Chinese remainder theorem combines the exponent-uniform prime-power
bounds. The finitely many primes over 3 contribute a field-dependent constant;
the remaining factors are bounded by the square of the ideal divisor product.
-/

noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 200000
open scoped NumberField BigOperators Classical
open UniqueFactorizationMonoid

namespace WaringSiegel

/-- Cubing kernels commute with finite products. -/
theorem cubeUnitKernelCard_pi {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Monoid (A i)] :
    cubeUnitKernelCard (∀ i, A i) = ∏ i, cubeUnitKernelCard (A i) := by
  let e : {u : (∀ i, A i)ˣ // u ^ 3 = 1} ≃ ∀ i, {u : (A i)ˣ // u ^ 3 = 1} :=
    { toFun := fun u i => ⟨⟨u.val.val i, u.val.inv i,
        congrFun u.val.val_inv i, congrFun u.val.inv_val i⟩, by
        apply Units.ext
        have h := congrArg (fun z : (∀ i, A i)ˣ => z.val i) u.property
        simpa only [Units.val_pow_eq_pow_val, Units.val_one, Pi.pow_apply, Pi.one_apply] using h⟩
      invFun := fun f => ⟨⟨fun i => (f i).val.val, fun i => (f i).val.inv,
        funext (fun i => (f i).val.val_inv), funext (fun i => (f i).val.inv_val)⟩, by
        apply Units.ext
        funext i
        have h := congrArg (fun z : (A i)ˣ => z.val) (f i).property
        simpa only [Units.val_pow_eq_pow_val, Units.val_one, Pi.pow_apply, Pi.one_apply] using h⟩
      left_inv := fun u => by apply Subtype.ext; apply Units.ext; rfl
      right_inv := fun f => by funext i; apply Subtype.ext; apply Units.ext; rfl }
  exact (Nat.card_congr e).trans Nat.card_pi

variable {K : Type*} [Field K] [NumberField K]

def normalizedFactorCompletionPrime (P : Ideal (𝓞 K)) (hp : Prime P) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  ⟨P, Ideal.isPrime_of_prime hp, hp.ne_zero⟩

def cubicPrimeKernelConstant (P : Ideal (𝓞 K)) : ℕ :=
  if hp : Prime P then
    if (3 : 𝓞 K) ∈ P then
      (Ideal.absNorm P) ^
        cubicLocalPrecision ((normalizedFactorCompletionPrime P hp).adicCompletionIntegers K)
    else 1
  else 1

theorem cubicPrimeKernelConstant_one_le (P : Ideal (𝓞 K)) :
    1 ≤ cubicPrimeKernelConstant P := by
  unfold cubicPrimeKernelConstant
  split_ifs with hp h3
  · apply Nat.one_le_pow _ _
    exact Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hp.ne_zero)
  all_goals exact le_rfl

theorem cubicPrimeKernelConstant_eq_one (P : Ideal (𝓞 K))
    (h3 : (3 : 𝓞 K) ∉ P) : cubicPrimeKernelConstant P = 1 := by
  simp [cubicPrimeKernelConstant, h3]

/-- Each prime-power kernel is controlled by the local bad-prime constant and multiplicity. -/
theorem primePower_kernel_le_divisor_square (P : Ideal (𝓞 K)) (hp : Prime P)
    (e : ℕ) (he : 0 < e) :
    cubeUnitKernelCard (𝓞 K ⧸ P ^ e) ≤ cubicPrimeKernelConstant P * (e + 1) ^ 2 := by
  let v := normalizedFactorCompletionPrime P hp
  by_cases h3 : (3 : 𝓞 K) ∈ P
  · have h := primePower_cube_unit_kernel_uniform_bound v e
    have hC : cubicPrimeKernelConstant P =
        (Ideal.absNorm P) ^ cubicLocalPrecision (v.adicCompletionIntegers K) := by
      simp [cubicPrimeKernelConstant, hp, h3, v]
    change cubeUnitKernelCard (𝓞 K ⧸ P ^ e) ≤
      (Ideal.absNorm P) ^ cubicLocalPrecision (v.adicCompletionIntegers K) at h
    rw [← hC] at h
    exact h.trans (Nat.le_mul_of_pos_right _ (by positivity))
  · rw [cubicPrimeKernelConstant_eq_one P h3, one_mul]
    have h := primePower_cube_unit_kernel_le_three v h3 e
    exact h.trans (by nlinarith)

/-- The finite exceptional product is independent of the modulus. -/
def cubicGlobalKernelConstant : ℕ :=
  ∏ P ∈ (IdealDivisorBounds.idealDivisors_finite
    (Ideal.span ({(3 : 𝓞 K)} : Set (𝓞 K)))
    (mt Ideal.span_singleton_eq_bot.mp (by norm_num))).toFinset,
      cubicPrimeKernelConstant P

theorem cubicGlobalKernelConstant_pos : 0 < cubicGlobalKernelConstant (K := K) := by
  unfold cubicGlobalKernelConstant
  exact Finset.prod_pos (fun P _ => lt_of_lt_of_le Nat.zero_lt_one (cubicPrimeKernelConstant_one_le P))

theorem cubicPrimeKernelConstant_product_le (S : Finset (Ideal (𝓞 K))) :
    (∏ P ∈ S, cubicPrimeKernelConstant P) ≤ cubicGlobalKernelConstant (K := K) := by
  let B := (IdealDivisorBounds.idealDivisors_finite
    (Ideal.span ({(3 : 𝓞 K)} : Set (𝓞 K)))
    (mt Ideal.span_singleton_eq_bot.mp (by norm_num))).toFinset
  have hfilter : (∏ P ∈ S, cubicPrimeKernelConstant P) =
      ∏ P ∈ S.filter (fun P => P ∈ B), cubicPrimeKernelConstant P := by
    apply (Finset.prod_filter_of_ne (fun P hP hne => ?_)).symm
    by_contra hnot
    have h3 : (3 : 𝓞 K) ∉ P := by
      intro h3
      apply hnot
      apply (IdealDivisorBounds.idealDivisors_finite
        (Ideal.span ({(3 : 𝓞 K)} : Set (𝓞 K)))
        (mt Ideal.span_singleton_eq_bot.mp (by norm_num))).mem_toFinset.mpr
      change P ∣ Ideal.span ({(3 : 𝓞 K)} : Set (𝓞 K))
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact h3
    exact hne (cubicPrimeKernelConstant_eq_one P h3)
  rw [hfilter]
  change _ ≤ ∏ P ∈ B, cubicPrimeKernelConstant P
  exact Finset.prod_le_prod_of_subset_of_one_le'
    (by intro P hP; exact (Finset.mem_filter.mp hP).2)
    (fun P _ _ => cubicPrimeKernelConstant_one_le P)

/-- Exact CRT factorization for the actual unit-cubing kernel. -/
theorem ideal_cube_unit_kernel_factorization (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    cubeUnitKernelCard (𝓞 K ⧸ I) =
      ∏ P ∈ (normalizedFactors I).toFinset,
        cubeUnitKernelCard (𝓞 K ⧸ P ^ (normalizedFactors I).count P) := by
  let S := (normalizedFactors I).toFinset
  let e : (𝓞 K ⧸ I) ≃+* ∀ P : S,
      𝓞 K ⧸ P.val ^ (normalizedFactors I).count P.val :=
    IsDedekindDomain.quotientEquivPiOfFinsetProdEq I id
      (fun P => (normalizedFactors I).count P)
      (fun P hP => prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
      (fun P _ Q _ h => h) (by
        rw [← Finset.prod_multiset_map_count, Multiset.map_id, prod_normalizedFactors_eq_self hI])
  rw [cubeUnitKernelCard_congr e.toMulEquiv, cubeUnitKernelCard_pi]
  exact Finset.prod_coe_sort S
    (fun P => cubeUnitKernelCard (𝓞 K ⧸ P ^ (normalizedFactors I).count P))

theorem ideal_cube_unit_kernel_le_divisor_square (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    cubeUnitKernelCard (𝓞 K ⧸ I) ≤ cubicGlobalKernelConstant (K := K) *
      (∏ P ∈ (normalizedFactors I).toFinset, ((normalizedFactors I).count P + 1)) ^ 2 := by
  rw [ideal_cube_unit_kernel_factorization I hI]
  calc
    _ ≤ ∏ P ∈ (normalizedFactors I).toFinset,
        cubicPrimeKernelConstant P * ((normalizedFactors I).count P + 1) ^ 2 := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro P hP
      exact primePower_kernel_le_divisor_square P
        (prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)) _
        (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hP))
    _ = (∏ P ∈ (normalizedFactors I).toFinset, cubicPrimeKernelConstant P) *
        (∏ P ∈ (normalizedFactors I).toFinset, ((normalizedFactors I).count P + 1)) ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow]
    _ ≤ _ := Nat.mul_le_mul_right _ (cubicPrimeKernelConstant_product_le _)

/-- The cubing kernel on actual residue-ring units has epsilon growth in the
absolute norm, uniformly over every nonzero integral ideal. -/
theorem ideal_cube_unit_kernel_epsilon_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 K), I ≠ 0 →
      (cubeUnitKernelCard (𝓞 K ⧸ I) : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBounds.ideal_divisor_product_le_rpow
    (K := K) (show 0 < ε / 2 by positivity)
  have hG : 0 < (cubicGlobalKernelConstant (K := K) : ℝ) := by
    exact_mod_cast cubicGlobalKernelConstant_pos (K := K)
  refine ⟨(cubicGlobalKernelConstant (K := K) : ℝ) * C ^ 2, by positivity, ?_⟩
  intro I hI
  have hD := hdiv I hI
  have hk : (cubeUnitKernelCard (𝓞 K ⧸ I) : ℝ) ≤
      (cubicGlobalKernelConstant (K := K) : ℝ) *
        (∏ P ∈ (normalizedFactors I).toFinset,
          ((normalizedFactors I).count P + 1 : ℝ)) ^ 2 := by
    exact_mod_cast ideal_cube_unit_kernel_le_divisor_square I hI
  calc
    _ ≤ (cubicGlobalKernelConstant (K := K) : ℝ) *
        (C * (Ideal.absNorm I : ℝ) ^ (ε / 2)) ^ 2 :=
      hk.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hD 2) hG.le)
    _ = ((cubicGlobalKernelConstant (K := K) : ℝ) * C ^ 2) *
        (Ideal.absNorm I : ℝ) ^ ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
      norm_num
      ring

end WaringSiegel

#print axioms WaringSiegel.ideal_cube_unit_kernel_le_divisor_square

#print axioms WaringSiegel.ideal_cube_unit_kernel_epsilon_bound
