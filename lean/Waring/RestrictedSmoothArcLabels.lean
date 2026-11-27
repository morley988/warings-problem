import Waring.RestrictedSmoothArcPacking

/-! # Reduced-residue labels and the actual disjoint arc sum -/

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Waring.RestrictedSmoothArcs

abbrev ArcLabel := Σ q : ℕ+, (ZMod (q : ℕ))ˣ

def arcLabelRat (p : ArcLabel) : ℚ where
  num := ((p.2 : ZMod (p.1 : ℕ)).val : ℤ)
  den := (p.1 : ℕ)
  den_nz := p.1.pos.ne'
  reduced := by simpa only [Int.natAbs_natCast] using ZMod.val_coe_unit_coprime p.2

theorem arcLabelRat_den (p : ArcLabel) : (arcLabelRat p).den=(p.1 : ℕ) := rfl

theorem arcLabelRat_real (p : ArcLabel) :
    (arcLabelRat p : ℝ)=((p.2 : ZMod (p.1 : ℕ)).val : ℝ)/(p.1 : ℝ) := by
  simp [Rat.cast_def,arcLabelRat]

theorem arcLabelRat_injective : Function.Injective arcLabelRat := by
  intro p q he
  rcases p with ⟨p,a⟩
  rcases q with ⟨q,b⟩
  have hq : (p : ℕ)=(q : ℕ) := congrArg Rat.den he
  have hpq : p=q := Subtype.ext hq
  subst q
  have hn : ((a : ZMod (p : ℕ)).val : ℤ)=((b : ZMod (p : ℕ)).val : ℤ) :=
    congrArg Rat.num he
  have hab : a=b := by
    apply Units.ext
    apply ZMod.val_injective
    exact_mod_cast hn
  subst b
  rfl

theorem arcLabelRat_bounds (p : ArcLabel) :
    (0 : ℝ) ≤ arcLabelRat p ∧ (arcLabelRat p : ℝ) ≤ 1 := by
  have hq : 0 < (p.1 : ℝ) := by exact_mod_cast p.1.pos
  rw [arcLabelRat_real]
  refine ⟨div_nonneg (Nat.cast_nonneg _) hq.le,?_⟩
  apply (div_le_one hq).mpr
  exact_mod_cast (ZMod.val_lt (p.2 : ZMod (p.1 : ℕ))).le

def arcLabelIntegral (p : ArcLabel) (F : ℝ → ℝ) (δ : ℝ) : ℝ :=
  ∫ β in -(δ/(p.1 : ℝ))..δ/(p.1 : ℝ),
    F (((p.2 : ZMod (p.1 : ℕ)).val : ℝ)/(p.1 : ℝ)+β)

theorem arcLabelIntegral_eq (p : ArcLabel) (F : ℝ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    arcLabelIntegral p F δ = ∫ x in rationalBand (arcLabelRat p) δ, F x := by
  rw [rationalBand_integral_eq _ hδ,arcLabelRat_real]
  rfl

/-- A finite family of the literal reduced-residue interval integrals
has no multiplicity loss under the source disjointness condition. -/
theorem sum_arcLabelIntegral_le (A : Finset ArcLabel) {Q δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*Q*δ ≤ 1)
    (hQ : ∀ p ∈ A, (p.1 : ℝ) ≤ Q)
    {F : ℝ → ℝ} (hF : Continuous F) (hper : Function.Periodic F 1)
    (hF0 : ∀ x, 0 ≤ F x) :
    (∑ p ∈ A, arcLabelIntegral p F δ) ≤ 3*∫ x in (0 : ℝ)..1, F x := by
  classical
  have H := sum_rationalBand_integrals_le (A.image arcLabelRat) hδ hδ1 hsmall
    (by
      intro r hr
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
      exact ⟨hQ p hp,(arcLabelRat_bounds p).1,(arcLabelRat_bounds p).2⟩)
    hF hper hF0
  rw [Finset.sum_image (fun _ _ _ _ he => arcLabelRat_injective he)] at H
  simpa only [arcLabelIntegral_eq _ _ hδ] using H

#print axioms sum_arcLabelIntegral_le
end Waring.RestrictedSmoothArcs
