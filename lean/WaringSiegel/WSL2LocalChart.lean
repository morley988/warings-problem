import WaringSiegel.WSL2LocalLift

/-!
# A bijective cubic correction chart on the maximal ideal

The scaled correction `3t³ + 3xt² + x²t` for a unit `x` permutes the maximal
ideal of a Henselian local ring. It preserves every ideal congruence exactly.
This supplies a rigorous local inverse with controlled precision even at 3.
-/

noncomputable section

open IsLocalRing

namespace WaringSiegel

def cubicCorrection {R : Type*} [CommRing R] (x t : R) : R :=
  3 * t ^ 3 + 3 * x * t ^ 2 + x ^ 2 * t

theorem cubicCorrection_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] (x : R)
    {t : R} (ht : t ∈ maximalIdeal R) : cubicCorrection x t ∈ maximalIdeal R := by
  apply (residue_eq_zero_iff _).mp
  have ht0 := (residue_eq_zero_iff t).mpr ht
  simp [cubicCorrection, ht0]

theorem cubicCorrection_sub_mem_iff
    {R : Type*} [CommRing R] [IsLocalRing R] {x t u : R}
    (hx : IsUnit x) (ht : t ∈ maximalIdeal R) (hu : u ∈ maximalIdeal R)
    (I : Ideal R) :
    cubicCorrection x t - cubicCorrection x u ∈ I ↔ t - u ∈ I := by
  let B : R := x ^ 2 + 3 * x * (t + u) + 3 * (t ^ 2 + t * u + u ^ 2)
  have hB : IsUnit B := by
    apply (residue_ne_zero_iff_isUnit B).mp
    have ht0 := (residue_eq_zero_iff t).mpr ht
    have hu0 := (residue_eq_zero_iff u).mpr hu
    have hBeq : residue R B = residue R x ^ 2 := by simp [B, ht0, hu0]
    rw [hBeq]
    exact pow_ne_zero _ ((residue_ne_zero_iff_isUnit x).mpr hx)
  have hfactor : cubicCorrection x t - cubicCorrection x u = B * (t - u) := by
    dsimp [cubicCorrection, B]
    ring
  rw [hfactor, I.unit_mul_mem_iff_mem hB]

def cubicCorrectionMap
    {R : Type*} [CommRing R] [IsLocalRing R] (x : R) :
    maximalIdeal R → maximalIdeal R :=
  fun t => ⟨cubicCorrection x t, cubicCorrection_mem_maximalIdeal x t.property⟩

theorem cubicCorrectionMap_bijective
    {R : Type*} [CommRing R] [HenselianLocalRing R] {x : R} (hx : IsUnit x) :
    Function.Bijective (cubicCorrectionMap x) := by
  constructor
  · intro t u h
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hg : cubicCorrection x t - cubicCorrection x u ∈ (⊥ : Ideal R) := by
      rw [Ideal.mem_bot, sub_eq_zero]
      exact congrArg Subtype.val h
    simpa only [Ideal.mem_bot] using
      (cubicCorrection_sub_mem_iff hx t.property u.property (⊥ : Ideal R)).mp hg
  · intro c
    obtain ⟨t, ht, he⟩ := cubic_correction_surjective hx c.property
    exact ⟨⟨t, ht⟩, Subtype.ext he⟩

def cubicCorrectionEquiv
    {R : Type*} [CommRing R] [HenselianLocalRing R] {x : R} (hx : IsUnit x) :
    maximalIdeal R ≃ maximalIdeal R :=
  Equiv.ofBijective (cubicCorrectionMap x) (cubicCorrectionMap_bijective hx)

/-- The correction chart is a permutation at every ideal precision, rather
than merely a surjection on the completed ring. -/
def cubicCorrectionQuotientEquiv
    {R : Type*} [CommRing R] [HenselianLocalRing R] {x : R}
    (hx : IsUnit x) (I : Ideal R) :
    ((maximalIdeal R) ⧸ Submodule.comap (maximalIdeal R).subtype I) ≃
      ((maximalIdeal R) ⧸ Submodule.comap (maximalIdeal R).subtype I) :=
  Quotient.congr (cubicCorrectionEquiv hx) (by
    intro t u
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    change (t : R) - (u : R) ∈ I ↔ cubicCorrection x t - cubicCorrection x u ∈ I
    exact (cubicCorrection_sub_mem_iff hx t.property u.property I).symm)

theorem cubicCorrection_quotient_unique
    {R : Type*} [CommRing R] [HenselianLocalRing R] {x : R}
    (hx : IsUnit x) (I : Ideal R)
    (c : (maximalIdeal R) ⧸ Submodule.comap (maximalIdeal R).subtype I) :
    ∃! t, cubicCorrectionQuotientEquiv hx I t = c := by
  refine ⟨(cubicCorrectionQuotientEquiv hx I).symm c, ?_, ?_⟩
  · exact (cubicCorrectionQuotientEquiv hx I).apply_symm_apply c
  · intro t ht
    exact (cubicCorrectionQuotientEquiv hx I).injective
      (ht.trans ((cubicCorrectionQuotientEquiv hx I).apply_symm_apply c).symm)

theorem cube_scaled_difference
    {R : Type*} [CommRing R] (x t u : R) :
    (x + 3 * t) ^ 3 - (x + 3 * u) ^ 3 =
      9 * (cubicCorrection x t - cubicCorrection x u) := by
  dsimp [cubicCorrection]
  ring

/-- Cubing on the local chart loses exactly the factor 9 in precision. -/
theorem cube_scaled_sub_mem_iff
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {x t u : R} (hx : IsUnit x) (ht : t ∈ maximalIdeal R)
    (hu : u ∈ maximalIdeal R) (h9 : (9 : R) ≠ 0) (I : Ideal R) :
    (x + 3 * t) ^ 3 - (x + 3 * u) ^ 3 ∈ Ideal.span ({9} : Set R) * I ↔
      t - u ∈ I := by
  rw [cube_scaled_difference, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨c, hc, he⟩
    have he' : c = cubicCorrection x t - cubicCorrection x u := mul_left_cancel₀ h9 he
    rw [he'] at hc
    exact (cubicCorrection_sub_mem_iff hx ht hu I).mp hc
  · intro htu
    exact ⟨_, (cubicCorrection_sub_mem_iff hx ht hu I).mpr htu, rfl⟩

end WaringSiegel

#print axioms WaringSiegel.cubicCorrectionMap_bijective
#print axioms WaringSiegel.cubicCorrection_quotient_unique
#print axioms WaringSiegel.cube_scaled_sub_mem_iff
