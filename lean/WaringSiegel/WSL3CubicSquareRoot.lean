import WaringSiegel.WSL3CubicMulCharacters

/-! # WSL3: the square-root estimate for pure cubic finite-field sums

The proof uses multiplicative Fourier expansion and exact Gauss-sum norms.
It does not assert a bound for a cubic sum with an arbitrary linear twist.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace WaringSiegel
variable {F : Type*} [Field F] [Fintype F]
variable [Fintype (MulChar F ℂ)]

def finiteFieldPowerCharacters (F : Type*) [Field F] [Fintype F]
    [Fintype (MulChar F ℂ)] (k : ℕ) : Finset (MulChar F ℂ) :=
  Finset.univ.filter (fun χ => χ^k = 1)

theorem finite_field_power_characters_card_le (k : ℕ) (hk : 0 < k) :
    (finiteFieldPowerCharacters F k).card ≤ k := by
  let e := (MulChar.mulEquiv_units F ℂ).some
  letI : IsCyclic (MulChar F ℂ) := isCyclic_of_injective e.toMonoidHom e.injective
  have hc : (finiteFieldPowerCharacters F k).card =
      Nat.card (powMonoidHom k : MulChar F ℂ →* MulChar F ℂ).ker := by
    simp only [finiteFieldPowerCharacters, Nat.card_eq_fintype_card,
      Fintype.card_subtype, MonoidHom.mem_ker, powMonoidHom_apply]
  rw [hc, IsCyclic.card_powMonoidHom_ker]
  exact Nat.gcd_le_right _ hk

theorem finite_field_nontrivial_power_characters_card_le (k : ℕ) (hk : 0 < k) :
    ((finiteFieldPowerCharacters F k).erase 1).card ≤ k - 1 := by
  have hc := finite_field_power_characters_card_le (F := F) k hk
  have hmem : (1 : MulChar F ℂ) ∈ finiteFieldPowerCharacters F k := by
    simp [finiteFieldPowerCharacters]
  rw [Finset.card_erase_of_mem hmem]
  omega

theorem finite_field_gauss_units_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    (∑ v : Fˣ, ψ v * χ v) = gaussSum χ ψ := by
  rw [finite_field_units_sum_eq (fun x : F => ψ x * χ x)]
  simp only [χ.map_zero, mul_zero, zero_mul, sub_zero, gaussSum, mul_comm]

theorem finite_field_gauss_trivial (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum (1 : MulChar F ℂ) ψ = -1 := by
  rw [← finite_field_gauss_units_sum]
  simp only [MulChar.one_apply_coe, mul_one]
  rw [finite_field_units_sum_eq ψ]
  have hn : ψ ≠ 1 := by simpa using hψ (one_ne_zero : (1 : F) ≠ 0)
  rw [AddChar.sum_eq_zero_of_ne_one hn, ψ.map_zero_eq_one, zero_sub]

theorem finite_field_power_sum_gauss (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (k : ℕ) (hk : 0 < k) :
    (∑ x : F, ψ (x^k)) =
      ∑ χ ∈ ((finiteFieldPowerCharacters F k).erase 1), gaussSum χ ψ := by
  have hp := finite_field_mulChar_power_expansion (fun u : Fˣ => ψ u) k
  have hu : (∑ u : Fˣ, ψ ((u : F)^k)) =
      ∑ χ ∈ finiteFieldPowerCharacters F k, gaussSum χ ψ := by
    simpa only [Units.val_pow_eq_pow_val, finite_field_gauss_units_sum,
      finiteFieldPowerCharacters, Finset.sum_filter] using hp
  rw [finite_field_units_sum_eq (fun x : F => ψ (x^k)),
    zero_pow (Nat.ne_of_gt hk), ψ.map_zero_eq_one] at hu
  have hmem : (1 : MulChar F ℂ) ∈ finiteFieldPowerCharacters F k := by
    simp [finiteFieldPowerCharacters]
  have he := Finset.sum_erase_add (finiteFieldPowerCharacters F k)
    (fun χ : MulChar F ℂ => gaussSum χ ψ) hmem
  dsimp only at he
  rw [finite_field_gauss_trivial ψ hψ] at he
  linear_combination hu - he

/-- Square-root cancellation for every pure power, with its exact elementary degree loss. -/
theorem finite_field_power_sum_norm_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (k : ℕ) (hk : 0 < k) :
    ‖∑ x : F, ψ (x^k)‖ ≤ (k - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ) := by
  rw [finite_field_power_sum_gauss ψ hψ k hk]
  calc
    _ ≤ ∑ χ ∈ ((finiteFieldPowerCharacters F k).erase 1), ‖gaussSum χ ψ‖ :=
      norm_sum_le _ _
    _ = ((finiteFieldPowerCharacters F k).erase 1).card *
        Real.sqrt (Fintype.card F : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro χ hχ
      exact complex_gaussSum_norm χ (Finset.mem_erase.mp hχ).1 ψ hψ
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast finite_field_nontrivial_power_characters_card_le (F := F) k hk)
      (Real.sqrt_nonneg _)

omit [Fintype (MulChar F ℂ)] in
/-- The actual pure cubic sum has absolute value at most `2 √q`, in every finite field. -/
theorem finite_field_cubic_sum_norm_le_two_sqrt
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) {a : F} (ha : a ≠ 0) :
    ‖finiteFieldCubicSum ψ a‖ ≤ 2 * Real.sqrt (Fintype.card F : ℝ) := by
  letI : Fintype (MulChar F ℂ) := Fintype.ofFinite _
  have h := finite_field_power_sum_norm_le (ψ.mulShift a)
    (AddChar.IsPrimitive.of_ne_one (hψ ha)) 3 (by decide)
  simpa only [finiteFieldCubicSum, AddChar.mulShift_apply, Nat.reduceSub,
    Nat.cast_ofNat] using h

end WaringSiegel

#print axioms WaringSiegel.finite_field_cubic_sum_norm_le_two_sqrt
