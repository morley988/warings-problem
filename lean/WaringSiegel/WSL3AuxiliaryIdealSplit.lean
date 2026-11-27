import WaringSiegel.WSL3ConductorFactorization

/-! # Actual good/bad prime factorization of an auxiliary common modulus -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem mem_idealPrimeSupport_iff_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    v ∈ idealPrimeSupport I hI ↔ v.asIdeal ∣ I := by
  exact (Ideal.finite_factors hI).mem_toFinset

theorem idealPrimeSupport_mono_of_le (M P : Ideal (𝓞 K)) (hM : M ≠ 0) (hP : P ≠ 0)
    (hMP : M ≤ P) : idealPrimeSupport P hP ⊆ idealPrimeSupport M hM := by
  intro v hv
  apply (mem_idealPrimeSupport_iff_dvd M hM v).mpr
  exact dvd_trans ((mem_idealPrimeSupport_iff_dvd P hP v).mp hv) (Ideal.dvd_iff_le.mpr hMP)

theorem idealPrimeExponent_mono_of_le (M P : Ideal (𝓞 K)) (hM : M ≠ 0) (hP : P ≠ 0)
    (hMP : M ≤ P) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    idealPrimeExponent P v ≤ idealPrimeExponent M v := by
  obtain ⟨J,hJ⟩ := Ideal.dvd_iff_le.mpr hMP
  have hJ0 : J ≠ 0 := by intro hz; exact hM (by rw [hJ,hz,mul_zero])
  rw [hJ,idealPrimeExponent_mul P J hP hJ0]
  exact Nat.le_add_right _ _

def auxiliaryGoodIdeal (M : Ideal (𝓞 K)) (hM : M ≠ 0) (P : Ideal (𝓞 K)) (hP : P ≠ 0) :
    Ideal (𝓞 K) := ∏ v ∈ idealPrimeSupport M hM \ idealPrimeSupport P hP, v.asIdeal^idealPrimeExponent M v

def auxiliaryBadIdeal (M P : Ideal (𝓞 K)) (hP : P ≠ 0) : Ideal (𝓞 K) :=
  ∏ v ∈ idealPrimeSupport P hP, v.asIdeal^idealPrimeExponent M v

theorem auxiliaryGoodIdeal_ne_zero (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (P : Ideal (𝓞 K)) (hP : P ≠ 0) : auxiliaryGoodIdeal M hM P hP ≠ 0 :=
  prime_power_product_ne_zero _ _

theorem auxiliaryBadIdeal_ne_zero (M P : Ideal (𝓞 K)) (hP : P ≠ 0) :
    auxiliaryBadIdeal M P hP ≠ 0 := prime_power_product_ne_zero _ _

theorem auxiliaryGoodIdeal_mul_bad (M P : Ideal (𝓞 K)) (hM : M ≠ 0) (hP : P ≠ 0)
    (hMP : M ≤ P) : auxiliaryGoodIdeal M hM P hP * auxiliaryBadIdeal M P hP = M := by
  unfold auxiliaryGoodIdeal auxiliaryBadIdeal
  rw [Finset.prod_sdiff (idealPrimeSupport_mono_of_le M P hM hP hMP),idealPrimeSupport_factorization]

theorem auxiliaryBadIdeal_le (M P : Ideal (𝓞 K)) (hM : M ≠ 0) (hP : P ≠ 0)
    (hMP : M ≤ P) : auxiliaryBadIdeal M P hP ≤ P := by
  have hh : auxiliaryBadIdeal M P hP ≤
      ∏ v ∈ idealPrimeSupport P hP, v.asIdeal^idealPrimeExponent P v :=
    Finset.prod_le_prod' (fun v _ => Ideal.pow_le_pow_right
      (idealPrimeExponent_mono_of_le M P hM hP hMP v))
  exact hh.trans_eq (idealPrimeSupport_factorization P hP)

theorem prime_power_products_coprime_of_disjoint
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (r e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ) (hST : Disjoint S T) :
    IsCoprime (∏ v ∈ S, v.asIdeal^r v) (∏ v ∈ T, v.asIdeal^e v) := by
  apply IsCoprime.prod_left
  intro v hv
  apply IsCoprime.prod_right
  intro w hw
  exact heightOne_prime_powers_coprime v w (fun he =>
    (Finset.disjoint_left.mp hST) hv (he.symm ▸ hw)) _ _

theorem auxiliaryGoodIdeal_coprime_bad (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (P : Ideal (𝓞 K)) (hP : P ≠ 0) :
    IsCoprime (auxiliaryGoodIdeal M hM P hP) (auxiliaryBadIdeal M P hP) := by
  apply prime_power_products_coprime_of_disjoint
  exact Finset.disjoint_left.mpr (fun v hv hw => (Finset.mem_sdiff.mp hv).2 hw)

theorem auxiliaryGoodIdeal_coprime_mask (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (P : Ideal (𝓞 K)) (hP : P ≠ 0) :
    IsCoprime (auxiliaryGoodIdeal M hM P hP) P := by
  have hh : IsCoprime (auxiliaryGoodIdeal M hM P hP)
      (∏ v ∈ idealPrimeSupport P hP, v.asIdeal^idealPrimeExponent P v) := by
    apply prime_power_products_coprime_of_disjoint
    exact Finset.disjoint_left.mpr (fun v hv hw => (Finset.mem_sdiff.mp hv).2 hw)
  simpa only [idealPrimeSupport_factorization] using hh

theorem isUnit_quotient_mk_of_coprime_span (J : Ideal (𝓞 K)) (p : 𝓞 K)
    (h : IsCoprime J (Ideal.span ({p}:Set (𝓞 K)))) : IsUnit (Ideal.Quotient.mk J p) := by
  obtain ⟨a,ha,b,hb,hab⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp hb
  have ha0 : Ideal.Quotient.mk J a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have he := congrArg (Ideal.Quotient.mk J) hab
  rw [(Ideal.Quotient.mk J).map_add a b,ha0,zero_add,(Ideal.Quotient.mk J).map_one,
    hc,(Ideal.Quotient.mk J).map_mul p c] at he
  exact isUnit_of_mul_eq_one _ _ he

/-- The product of the bad-prime norms costs no more than the full mask norm. -/
theorem idealPrimeSupport_norm_square_le (P : Ideal (𝓞 K)) (hP : P ≠ 0) :
    (∏ v ∈ idealPrimeSupport P hP, (Ideal.absNorm v.asIdeal : ℝ)^2) ≤
      (Ideal.absNorm P : ℝ)^2 := by
  have hle : P ≤ ∏ v ∈ idealPrimeSupport P hP, v.asIdeal := by
    calc
      P = ∏ v ∈ idealPrimeSupport P hP, v.asIdeal^idealPrimeExponent P v :=
        (idealPrimeSupport_factorization P hP).symm
      _ ≤ ∏ v ∈ idealPrimeSupport P hP, v.asIdeal := by
        apply Finset.prod_le_prod'
        intro v hv
        simpa only [pow_one] using Ideal.pow_le_pow_right (I:=v.asIdeal)
          (idealPrimeExponent_pos_of_mem P hP v hv)
  have hnP : 0 < Ideal.absNorm P := Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hP)
  have hn := Nat.le_of_dvd hnP (Ideal.absNorm_dvd_absNorm_of_le hle)
  have hr : (∏ v ∈ idealPrimeSupport P hP, (Ideal.absNorm v.asIdeal : ℝ)) ≤ (Ideal.absNorm P:ℝ) := by
    exact_mod_cast (show (∏ v ∈ idealPrimeSupport P hP, Ideal.absNorm v.asIdeal) ≤ Ideal.absNorm P by
      simpa only [map_prod] using hn)
  rw [Finset.prod_pow]
  exact pow_le_pow_left₀ (Finset.prod_nonneg (fun v _ => Nat.cast_nonneg _)) hr 2

end WaringSiegel
#print axioms WaringSiegel.auxiliaryGoodIdeal_mul_bad
#print axioms WaringSiegel.idealPrimeSupport_norm_square_le
