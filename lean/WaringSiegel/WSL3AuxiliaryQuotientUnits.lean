import WaringSiegel.WSL3AuxiliaryMaskCRT

/-! # WSL3: unit restrictions through actual ideal-power quotients -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel

/-- A quotient map whose kernel is nilpotent reflects units. The statement
is expressed with original ideals, so it applies at ramified prime powers. -/
theorem quotient_factor_isUnit_iff_of_power_le
    {R : Type*} [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)
    (n : ℕ) (hJI : J^n ≤ I) (x : R ⧸ I) :
    IsUnit (Ideal.Quotient.factor hIJ x) ↔ IsUnit x := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hx
    obtain ⟨u,hu⟩ := isUnit_iff_exists_inv.mp hx
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective u
    have hab : 1-a*b ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [(Ideal.Quotient.mk J).map_sub, (Ideal.Quotient.mk J).map_one,
        (Ideal.Quotient.mk J).map_mul]
      change 1 - Ideal.Quotient.mk J a * Ideal.Quotient.mk J b = 0
      change Ideal.Quotient.mk J a * Ideal.Quotient.mk J b = 1 at hu
      rw [hu, sub_self]
    have hn : IsNilpotent (Ideal.Quotient.mk I (1-a*b)) := by
      refine ⟨n, ?_⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hJI (Ideal.pow_mem_pow hab n)
    have hu := hn.isUnit_one_sub
    have he : 1 - Ideal.Quotient.mk I (1-a*b) =
        Ideal.Quotient.mk I a * Ideal.Quotient.mk I b := by
      simp only [map_sub, map_one, map_mul, sub_sub_cancel]
    rw [he] at hu
    exact isUnit_of_mul_isUnit_left hu
  · intro hx
    exact hx.map (Ideal.Quotient.factor hIJ)

theorem quotient_power_factor_isUnit_iff
    {R : Type*} [CommRing R] (I : Ideal R) (r e : ℕ) (he : 1 ≤ e) (her : e ≤ r)
    (x : R ⧸ I^r) :
    IsUnit (Ideal.Quotient.factor (Ideal.pow_le_pow_right her) x) ↔ IsUnit x := by
  apply quotient_factor_isUnit_iff_of_power_le (I^r) (I^e)
    (Ideal.pow_le_pow_right her) r
  rw [← pow_mul]
  exact Ideal.pow_le_pow_right (by nlinarith : r ≤ e*r)

theorem finiteMaskedPowerSum_factor_of_power_le
    {R : Type*} [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)
    (n : ℕ) (hJI : J^n ≤ I) [Fintype (R ⧸ I)]
    (ψ : AddChar (R ⧸ I) ℂ) (k : ℕ) :
    finiteMaskedPowerSum (Ideal.Quotient.factor hIJ) ψ k =
      finiteRingUnitPowerSum ψ k := by
  rw [finiteMaskedPowerSum_mask_congr _ (RingHom.id _) (fun x =>
    quotient_factor_isUnit_iff_of_power_le I J hIJ n hJI x), finiteMaskedPowerSum_id]

theorem finiteMaskedCubicCharacterTerm_factor_of_power_le
    {R : Type*} [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)
    (n : ℕ) (hJI : J^n ≤ I) [Fintype (R ⧸ I)]
    (ψ : AddChar (R ⧸ I) ℂ) (p b : R ⧸ I) :
    finiteMaskedCubicCharacterTerm (Ideal.Quotient.factor hIJ) p b ψ =
      finiteRingRestrictedCubicCharacterTerm p b ψ := by
  rw [finiteMaskedCubicCharacterTerm_mask_congr _ (RingHom.id _) (fun x =>
    quotient_factor_isUnit_iff_of_power_le I J hIJ n hJI x), finiteMaskedCubicCharacterTerm_id]

end WaringSiegel
#print axioms WaringSiegel.quotient_power_factor_isUnit_iff
#print axioms WaringSiegel.finiteMaskedCubicCharacterTerm_factor_of_power_le
