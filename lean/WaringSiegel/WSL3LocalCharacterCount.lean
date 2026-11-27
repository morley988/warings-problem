import WaringSiegel.WSL3CubicDensitySharp
import WaringSiegel.WSL2TraceResidueCharacters
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! # WSL3: exact complete-character formulas over the actual residue rings

All additive characters are used, so these formulas also apply to ramified
and non-principal prime-power quotients without choosing a primitive character.
-/
noncomputable section
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {R : Type*} [CommRing R] [Fintype R]

def finiteRingPowerSum (ψ : AddChar R ℂ) (k : ℕ) : ℂ := ∑ x : R, ψ (x^k)

theorem ring_addChar_sum {ι : Type*} (ψ : AddChar R ℂ) (S : Finset ι) (f : ι → R) :
    ψ (∑ i ∈ S, f i) = ∏ i ∈ S, ψ (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, ψ.map_add_eq_mul, ih]

theorem finite_ring_power_sum_expansion (ψ : AddChar R ℂ) (k s : ℕ) (b : R) :
    finiteRingPowerSum ψ k ^ s * ψ (-b) =
      ∑ x : Fin s → R, ψ ((∑ i, x i^k) - b) := by
  rw [finiteRingPowerSum, Fintype.sum_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [← ring_addChar_sum, ← ψ.map_add_eq_mul, sub_eq_add_neg]

theorem finite_ring_power_character_count (k s : ℕ) (b : R) :
    (∑ ψ : AddChar R ℂ, finiteRingPowerSum ψ k ^ s * ψ (-b)) =
      (Fintype.card R : ℂ) *
        (Nat.card {x : Fin s → R // (∑ i, x i^k) = b} : ℂ) := by
  simp only [finite_ring_power_sum_expansion]
  rw [Finset.sum_comm]
  simp only [AddChar.sum_apply_eq_ite, sub_eq_zero, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  ring

theorem finite_ring_power_normalized_character_count (k s : ℕ) (hs : 1 ≤ s) (b : R) :
    (∑ ψ : AddChar R ℂ,
      (finiteRingPowerSum ψ k / (Fintype.card R : ℂ)) ^ s * ψ (-b)) =
      (Nat.card {x : Fin s → R // (∑ i, x i^k) = b} : ℂ) /
        (Fintype.card R : ℂ)^(s-1) := by
  have hq : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [div_pow, div_mul_eq_mul_div]
  rw [← Finset.sum_div, finite_ring_power_character_count]
  have he : s = (s-1)+1 := by omega
  rw [he, pow_succ]
  field_simp
  simp only [Nat.add_sub_cancel]

variable {K : Type*} [Field K] [NumberField K]

/-- The ordinary local factor at every finite precision is an exact sum of
normalized complete characters of `O_K / p^e`. -/
theorem primePower_cubic_normalized_character_formula
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K)
    [Fintype (𝓞 K ⧸ v.asIdeal^e)] :
    (normalizedPrimePowerCubicCount v 8 e ν : ℂ) =
      ∑ ψ : AddChar (𝓞 K ⧸ v.asIdeal^e) ℂ,
        (finiteRingPowerSum ψ 3 / (Ideal.absNorm (v.asIdeal^e) : ℂ))^8 *
          ψ (-Ideal.Quotient.mk (v.asIdeal^e) ν) := by
  have hc : Fintype.card (𝓞 K ⧸ v.asIdeal^e) = Ideal.absNorm (v.asIdeal^e) := by
    rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply]
    rfl
  rw [← hc, finite_ring_power_normalized_character_count 3 8 (by decide)]
  unfold normalizedPrimePowerCubicCount localCubicSolutionCount LocalCubicSolutions
  push_cast
  rw [hc, map_pow, Nat.cast_pow]
  norm_num
  rw [← pow_mul]
  rw [mul_comm e 7]

end WaringSiegel

#print axioms WaringSiegel.primePower_cubic_normalized_character_formula
