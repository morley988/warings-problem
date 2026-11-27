import WaringSiegel.WSL3AuxiliarySharpTail
import WaringSiegel.WSL3CubicSingularSeriesPositive

/-! # WSL3: literal finite auxiliary Fourier sums and local density products -/
noncomputable section
set_option maxHeartbeats 1000000
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def idealMaskedCubicSum (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (A : Ideal (𝓞 K)) (hIA : I ≤ A) (p ν : 𝓞 K) : ℂ :=
  letI := idealResidueFintype I hI
  ∑ ψ : AddChar (𝓞 K ⧸ I) ℂ,
    finiteMaskedCubicCharacterTerm (Ideal.Quotient.factor hIA)
      (Ideal.Quotient.mk I p) (Ideal.Quotient.mk I ν) ψ

def idealOrdinaryCubicSum (I : Ideal (𝓞 K)) (hI : I ≠ 0) (ν : 𝓞 K) : ℂ :=
  letI := idealResidueFintype I hI
  ∑ ψ : AddChar (𝓞 K ⧸ I) ℂ,
    finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk I ν) ψ

theorem idealMaskedCubicSum_unrestricted (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (p ν : 𝓞 K) (hp : IsUnit (Ideal.Quotient.mk I p)) :
    idealMaskedCubicSum I hI ⊤ le_top p ν = idealOrdinaryCubicSum I hI ν := by
  letI := idealResidueFintype I hI
  simp only [idealMaskedCubicSum, idealOrdinaryCubicSum,
    finiteMaskedCubicCharacterTerm_unrestricted _ _ _ _ hp]

theorem idealMaskedCubicSum_mul
    (I J A B : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : IsCoprime I J) (hIA : I ≤ A) (hJB : J ≤ B) (p ν : 𝓞 K) :
    idealMaskedCubicSum (I*J) (mul_ne_zero hI hJ) (A*B) (mul_le_mul' hIA hJB) p ν =
      idealMaskedCubicSum I hI A hIA p ν * idealMaskedCubicSum J hJ B hJB p ν := by
  letI := idealResidueFintype I hI
  letI := idealResidueFintype J hJ
  letI := idealResidueFintype (I*J) (mul_ne_zero hI hJ)
  unfold idealMaskedCubicSum
  rw [← (crtAddCharEquiv I J h).bijective.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro ψ _
  apply Finset.sum_congr rfl
  intro φ _
  exact finiteMaskedCubicCharacterTerm_crt I J A B h hIA hJB ψ φ p ν

theorem idealOrdinaryCubicSum_mul
    (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : IsCoprime I J) (ν : 𝓞 K) :
    idealOrdinaryCubicSum (I*J) (mul_ne_zero hI hJ) ν =
      idealOrdinaryCubicSum I hI ν * idealOrdinaryCubicSum J hJ ν := by
  have hu (L : Ideal (𝓞 K)) : IsUnit (Ideal.Quotient.mk L (1 : 𝓞 K)) := by
    rw [(Ideal.Quotient.mk L).map_one]; exact isUnit_one
  have he := idealMaskedCubicSum_mul I J ⊤ ⊤ hI hJ h le_top le_top (1 : 𝓞 K) ν
  have htt : (⊤ : Ideal (𝓞 K))*⊤ = ⊤ := by rw [← Ideal.one_eq_top, mul_one]
  simpa only [htt, idealMaskedCubicSum_unrestricted _ _ _ _ (hu _)] using he

theorem idealOrdinaryCubicSum_top (ν : 𝓞 K) :
    idealOrdinaryCubicSum ⊤ top_ne_bot ν = 1 := by
  let Q := 𝓞 K ⧸ (⊤ : Ideal (𝓞 K))
  letI := idealResidueFintype (⊤ : Ideal (𝓞 K)) top_ne_bot
  letI : Unique Q := { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  letI : Unique (AddChar Q ℂ) :=
    { default := 1
      uniq := by
        intro ψ
        ext x
        have hx : x = 0 := Subsingleton.elim _ _
        simp only [hx, ψ.map_zero_eq_one, AddChar.one_apply] }
  have happ (ψ : AddChar (𝓞 K ⧸ (⊤ : Ideal (𝓞 K))) ℂ)
      (x : 𝓞 K ⧸ (⊤ : Ideal (𝓞 K))) : ψ x = 1 := by
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx, ψ.map_zero_eq_one]
  simp [idealOrdinaryCubicSum, finiteRingPowerCharacterTerm,
    finiteRingPowerSum, happ, Fintype.card_unique]

theorem idealMaskedCubicSum_one (p ν : 𝓞 K) :
    idealMaskedCubicSum 1 one_ne_zero 1 le_rfl p ν = 1 := by
  have hp : IsUnit (Ideal.Quotient.mk (⊤ : Ideal (𝓞 K)) p) := by
    have he : Ideal.Quotient.mk (⊤ : Ideal (𝓞 K)) p = 1 := Subsingleton.elim _ _
    rw [he]; exact isUnit_one
  simpa only [Ideal.one_eq_top] using
    (idealMaskedCubicSum_unrestricted ⊤ top_ne_bot p ν hp).trans (idealOrdinaryCubicSum_top ν)

def primePowerMaskedCubicSum
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (r e : ℕ) (p ν : 𝓞 K) : ℂ :=
  if h : e ≤ r then idealMaskedCubicSum (v.asIdeal^r) (pow_ne_zero _ v.ne_bot)
    (v.asIdeal^e) (Ideal.pow_le_pow_right h) p ν else 0

theorem idealMaskedCubicSum_finset_prod
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (r e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ)
    (h : ∀ v ∈ S, e v ≤ r v) (p ν : 𝓞 K) :
    idealMaskedCubicSum (∏ v ∈ S, v.asIdeal^r v) (prime_power_product_ne_zero S r)
      (∏ v ∈ S, v.asIdeal^e v) (prime_power_product_le S r e h) p ν =
      ∏ v ∈ S, primePowerMaskedCubicSum v (r v) (e v) p ν := by
  induction S using Finset.induction_on with
  | empty => simpa using idealMaskedCubicSum_one (K := K) p ν
  | @insert v S hv ih =>
    have hS : ∀ w ∈ S, e w ≤ r w := fun w hw => h w (Finset.mem_insert_of_mem hw)
    have hcop : IsCoprime (v.asIdeal^r v) (∏ w ∈ S, w.asIdeal^r w) := by
      apply IsCoprime.prod_right
      intro w hw
      exact heightOne_prime_powers_coprime v w (fun he => hv (he ▸ hw)) _ _
    have heq := idealMaskedCubicSum_mul (v.asIdeal^r v)
      (∏ w ∈ S, w.asIdeal^r w) (v.asIdeal^e v) (∏ w ∈ S, w.asIdeal^e w)
      (pow_ne_zero _ v.ne_bot) (prime_power_product_ne_zero S r) hcop
      (Ideal.pow_le_pow_right (h v (Finset.mem_insert_self v S)))
      (prime_power_product_le S r e hS) p ν
    simp only [Finset.prod_insert hv]
    rw [heq, ih hS]
    simp only [primePowerMaskedCubicSum, dif_pos (h v (Finset.mem_insert_self v S))]

theorem primePowerMaskedCubicSum_eq_factor
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (r e : ℕ)
    (he : 1 ≤ e) (her : e ≤ r) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (p ν : 𝓞 K) (hp : p ∈ v.asIdeal) :
    primePowerMaskedCubicSum v r e p ν = (cubicModifiedResidueFactor v ν : ℂ) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  letI := idealResidueFintype (v.asIdeal^(n+1)) (pow_ne_zero _ v.ne_bot)
  unfold primePowerMaskedCubicSum
  rw [dif_pos her]
  unfold idealMaskedCubicSum
  have heq (ψ : AddChar (𝓞 K ⧸ v.asIdeal^(n+1)) ℂ) :=
    finiteMaskedCubicCharacterTerm_mask_congr
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right her)) (RingHom.id _)
      (fun x => quotient_power_factor_isUnit_iff v.asIdeal (n+1) e he her x)
      ψ (Ideal.Quotient.mk _ p) (Ideal.Quotient.mk _ ν)
  simp only [heq, finiteMaskedCubicCharacterTerm_id]
  rw [← primePower_restricted_cubic_character_formula,
    normalizedOriginalRestrictedCubicCount_eq_factor v h6 hp]

theorem idealMaskedCubicSum_bad_product
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (r e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ)
    (he : ∀ v ∈ S, 1 ≤ e v) (her : ∀ v ∈ S, e v ≤ r v)
    (h6 : ∀ v ∈ S, (6 : 𝓞 K) ∉ v.asIdeal) (p ν : 𝓞 K)
    (hp : ∀ v ∈ S, p ∈ v.asIdeal) :
    idealMaskedCubicSum (∏ v ∈ S, v.asIdeal^r v) (prime_power_product_ne_zero S r)
      (∏ v ∈ S, v.asIdeal^e v) (prime_power_product_le S r e her) p ν =
      ∏ v ∈ S, (cubicModifiedResidueFactor v ν : ℂ) := by
  rw [idealMaskedCubicSum_finset_prod S r e her]
  exact Finset.prod_congr rfl (fun v hv =>
    primePowerMaskedCubicSum_eq_factor v _ _ (he v hv) (her v hv) (h6 v hv) p ν (hp v hv))

theorem idealOrdinaryCubicSum_prime_power
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (r : ℕ) (ν : 𝓞 K) :
    idealOrdinaryCubicSum (v.asIdeal^r) (pow_ne_zero _ v.ne_bot) ν =
      (normalizedPrimePowerCubicCount v 8 r ν : ℂ) := by
  letI := idealResidueFintype (v.asIdeal^r) (pow_ne_zero _ v.ne_bot)
  rw [primePower_cubic_normalized_character_formula]
  have hc : Fintype.card (𝓞 K ⧸ v.asIdeal^r) = Ideal.absNorm (v.asIdeal^r) := by
    rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply]; rfl
  simp only [idealOrdinaryCubicSum, finiteRingPowerCharacterTerm, hc]

theorem idealOrdinaryCubicSum_finset_prod
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (r : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ) (ν : 𝓞 K) :
    idealOrdinaryCubicSum (∏ v ∈ S, v.asIdeal^r v) (prime_power_product_ne_zero S r) ν =
      ∏ v ∈ S, (normalizedPrimePowerCubicCount v 8 (r v) ν : ℂ) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Ideal.one_eq_top] using idealOrdinaryCubicSum_top ν
  | @insert v S hv ih =>
    have hcop : IsCoprime (v.asIdeal^r v) (∏ w ∈ S, w.asIdeal^r w) := by
      apply IsCoprime.prod_right
      intro w hw
      exact heightOne_prime_powers_coprime v w (fun he => hv (he ▸ hw)) _ _
    simp only [Finset.prod_insert hv]
    rw [idealOrdinaryCubicSum_mul _ _ (pow_ne_zero _ v.ne_bot)
      (prime_power_product_ne_zero S r) hcop, ih, idealOrdinaryCubicSum_prime_power]

end WaringSiegel
#print axioms WaringSiegel.idealMaskedCubicSum_bad_product
#print axioms WaringSiegel.idealOrdinaryCubicSum_finset_prod
