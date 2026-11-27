import WaringSiegel.WSL3OriginalUnitVanishing
import WaringSiegel.WSL3CubicAbsoluteCharacters

/-! # WSL3: restricted cubic character masses are nonnegative at target zero -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical ComplexConjugate NumberField
namespace WaringSiegel

theorem complex_even_pow_eq_norm_of_conj_eq {z : ℂ} (hz : conj z = z) (s : ℕ) :
    z^(2*s) = ((‖z‖^(2*s) : ℝ) : ℂ) := by
  have h := Complex.mul_conj' z
  rw [hz, ← pow_two, ← Complex.ofReal_pow] at h
  calc
    z^(2*s) = (z^2)^s := pow_mul z 2 s
    _ = (((‖z‖^2 : ℝ) : ℂ))^s := congrArg (fun x : ℂ => x^s) h
    _ = _ := by push_cast; rw [← pow_mul]

theorem finiteRingUnitCubicSum_conj {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) : conj (finiteRingUnitPowerSum ψ 3) = finiteRingUnitPowerSum ψ 3 := by
  have hterm (x : Rˣ) : conj (ψ ((x : R)^3)) = ψ (((-x : Rˣ) : R)^3) := by
    rw [← AddChar.inv_apply_eq_conj, ← ψ.map_neg_eq_inv, Units.val_neg]
    congr 1
    ring
  simp only [finiteRingUnitPowerSum, map_sum, hterm]
  exact (Equiv.neg Rˣ).bijective.sum_comp (fun x : Rˣ => ψ ((x : R)^3))

theorem finiteRingScaledCubicSum_conj {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (p : R) :
    conj (finiteRingScaledPowerSum ψ 3 p) = finiteRingScaledPowerSum ψ 3 p := by
  have hterm (x : R) : conj (ψ ((p*x)^3)) = ψ ((p*(-x))^3) := by
    rw [← AddChar.inv_apply_eq_conj, ← ψ.map_neg_eq_inv]
    congr 1
    ring
  simp only [finiteRingScaledPowerSum, map_sum, hterm]
  exact (Equiv.neg R).bijective.sum_comp (fun x : R => ψ ((p*x)^3))

/-- A term's absolute value is independent of the target, and its zero-target
value is already nonnegative. Thus no conductor-fiber cancellation is needed. -/
theorem finiteRingRestrictedCubicCharacterTerm_zero_eq_norm
    {R : Type*} [CommRing R] [Fintype R] (ψ : AddChar R ℂ) (p b : R) :
    finiteRingRestrictedCubicCharacterTerm p (0 : R) ψ =
      (‖finiteRingRestrictedCubicCharacterTerm p b ψ‖ : ℂ) := by
  let z : ℂ := finiteRingUnitPowerSum ψ 3 / (Fintype.card R : ℂ)
  let w : ℂ := finiteRingScaledPowerSum ψ 3 p / (Fintype.card R : ℂ)
  have hz : conj z = z := by
    simp only [z, map_div₀, finiteRingUnitCubicSum_conj, map_natCast]
  have hw : conj w = w := by
    simp only [w, map_div₀, finiteRingScaledCubicSum_conj, map_natCast]
  have hez : z^4 = ((‖z‖^4 : ℝ) : ℂ) := complex_even_pow_eq_norm_of_conj_eq hz 2
  have hew : w^4 = ((‖w‖^4 : ℝ) : ℂ) := complex_even_pow_eq_norm_of_conj_eq hw 2
  simp only [finiteRingRestrictedCubicCharacterTerm, neg_zero, ψ.map_zero_eq_one,
    mul_one, norm_mul, norm_pow, ψ.norm_apply, Complex.ofReal_mul]
  exact congrArg₂ (fun a b : ℂ => a*b) hez hew

theorem finiteRingRestrictedCubicCharacterTerm_finite_absolute_mass
    {R : Type*} [CommRing R] [Fintype R]
    (S : Finset (AddChar R ℂ)) (p b : R) :
    (∑ ψ ∈ S, ‖finiteRingRestrictedCubicCharacterTerm p b ψ‖) =
      ‖∑ ψ ∈ S, finiteRingRestrictedCubicCharacterTerm p (0 : R) ψ‖ := by
  have he : (∑ ψ ∈ S, finiteRingRestrictedCubicCharacterTerm p (0 : R) ψ) =
      ((∑ ψ ∈ S, ‖finiteRingRestrictedCubicCharacterTerm p b ψ‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun ψ _ => finiteRingRestrictedCubicCharacterTerm_zero_eq_norm ψ p b)
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]

end WaringSiegel
#print axioms WaringSiegel.finiteRingRestrictedCubicCharacterTerm_finite_absolute_mass
