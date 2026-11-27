import WaringSiegel.WSL3AuxiliaryLocalMass
import WaringSiegel.WSL3AuxiliaryOrdinaryMass

/-! # WSL3: exact finite ideal products for the auxiliary weighted mass -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def idealMaskedConductorMass (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (A : Ideal (𝓞 K)) (hIA : I ≤ A) (p ν : 𝓞 K) (t : ℝ) : ℝ :=
  letI := idealResidueFintype I hI
  finiteMaskedConductorMass I A hIA p ν t

theorem idealMaskedConductorMass_nonneg (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (A : Ideal (𝓞 K)) (hIA : I ≤ A) (p ν : 𝓞 K) (t : ℝ) :
    0 ≤ idealMaskedConductorMass I hI A hIA p ν t := by
  apply Finset.sum_nonneg
  intro ψ _
  positivity

theorem idealMaskedConductorMass_mul
    (I J A B : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : IsCoprime I J) (hIA : I ≤ A) (hJB : J ≤ B) (p ν : 𝓞 K) (t : ℝ) :
    idealMaskedConductorMass (I*J) (mul_ne_zero hI hJ) (A*B) (mul_le_mul' hIA hJB) p ν t =
      idealMaskedConductorMass I hI A hIA p ν t *
        idealMaskedConductorMass J hJ B hJB p ν t := by
  letI := idealResidueFintype I hI
  letI := idealResidueFintype J hJ
  letI := idealResidueFintype (I*J) (mul_ne_zero hI hJ)
  exact finiteMaskedConductorMass_crt I J A B h hIA hJB p ν t

theorem idealMaskedConductorMass_top (p ν : 𝓞 K) (t : ℝ) :
    idealMaskedConductorMass ⊤ top_ne_bot ⊤ le_rfl p ν t = 1 := by
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
  have hp : IsUnit (Ideal.Quotient.mk (⊤ : Ideal (𝓞 K)) p) := by
    have he : Ideal.Quotient.mk (⊤ : Ideal (𝓞 K)) p = 1 := Subsingleton.elim _ _
    rw [he]
    exact isUnit_one
  have hC (ψ : AddChar Q ℂ) : quotientCharacterConductor ⊤ ψ = ⊤ :=
    top_unique (ideal_le_quotientCharacterConductor ⊤ ψ)
  simp only [idealMaskedConductorMass, finiteMaskedConductorMass,
    finiteMaskedCubicCharacterTerm_unrestricted _ _ _ _ hp]
  simp [hC, ← Ideal.one_eq_top,
    finiteRingPowerCharacterTerm, finiteRingPowerSum, Fintype.card_unique]

theorem idealMaskedConductorMass_one (p ν : 𝓞 K) (t : ℝ) :
    idealMaskedConductorMass 1 one_ne_zero 1 le_rfl p ν t = 1 := by
  simpa only [Ideal.one_eq_top] using idealMaskedConductorMass_top (K := K) p ν t

theorem prime_power_product_le
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (r e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ)
    (h : ∀ v ∈ S, e v ≤ r v) :
    (∏ v ∈ S, v.asIdeal^r v) ≤ ∏ v ∈ S, v.asIdeal^e v := by
  exact Finset.prod_le_prod' (fun v hv => Ideal.pow_le_pow_right (h v hv))

def primePowerMaskedConductorMass
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (r e : ℕ) (p ν : 𝓞 K) (t : ℝ) : ℝ :=
  if h : e ≤ r then
    idealMaskedConductorMass (v.asIdeal^r) (pow_ne_zero _ v.ne_bot)
      (v.asIdeal^e) (Ideal.pow_le_pow_right h) p ν t
  else 0

theorem idealMaskedConductorMass_finset_prod
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (r e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ)
    (h : ∀ v ∈ S, e v ≤ r v) (p ν : 𝓞 K) (t : ℝ) :
    idealMaskedConductorMass (∏ v ∈ S, v.asIdeal^r v) (prime_power_product_ne_zero S r)
      (∏ v ∈ S, v.asIdeal^e v) (prime_power_product_le S r e h) p ν t =
      ∏ v ∈ S, primePowerMaskedConductorMass v (r v) (e v) p ν t := by
  induction S using Finset.induction_on with
  | empty => simpa using idealMaskedConductorMass_one (K := K) p ν t
  | @insert v S hv ih =>
    have hS : ∀ w ∈ S, e w ≤ r w := fun w hw => h w (Finset.mem_insert_of_mem hw)
    have hcop : IsCoprime (v.asIdeal^r v) (∏ w ∈ S, w.asIdeal^r w) := by
      apply IsCoprime.prod_right
      intro w hw
      exact heightOne_prime_powers_coprime v w (fun he => hv (he ▸ hw)) _ _
    have heq := idealMaskedConductorMass_mul (v.asIdeal^r v)
      (∏ w ∈ S, w.asIdeal^r w) (v.asIdeal^e v) (∏ w ∈ S, w.asIdeal^e w)
      (pow_ne_zero _ v.ne_bot) (prime_power_product_ne_zero S r) hcop
      (Ideal.pow_le_pow_right (h v (Finset.mem_insert_self v S)))
      (prime_power_product_le S r e hS) p ν t
    simp only [Finset.prod_insert hv]
    rw [heq, ih hS]
    simp only [primePowerMaskedConductorMass, dif_pos (h v (Finset.mem_insert_self v S))]

end WaringSiegel
#print axioms WaringSiegel.idealMaskedConductorMass_finset_prod
