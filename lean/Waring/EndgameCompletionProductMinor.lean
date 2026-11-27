import Waring.EndgameCompletionProductMomentBounds

/-!
# Minor-arc transport for the actual product-box weights

The ordinary minor moments are unconditional. The only hypotheses below
are the two intended smooth admissible excesses, supplied by the independent
seed and policy lanes. Product multiplicities are absorbed into their
arbitrarily small epsilon allowances before applying the actual Holder bound.
-/

noncomputable section
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology
namespace Waring.EndgameCompletion
open MixedEndgame SmoothMoments AdmissibleMinorArc

theorem productArcMoment_le_of_bound (k p L M : ℕ) {C exponent : ℝ} {A : Set ℝ}
    (hM : 1≤M) (hC : 0≤C) (hA : A⊆Set.Ioc 0 1)
    (h : productMoment k p L M≤C*((M : ℝ)^L)^exponent) :
    productArcMoment k p L M A≤ENNReal.ofReal C*ENNReal.ofReal ((M : ℝ)^L)^exponent := by
  have hp : 0<(M : ℝ)^L := pow_pos (by exact_mod_cast (show 0<M by omega)) _
  rw [ENNReal.ofReal_rpow_of_pos hp,← ENNReal.ofReal_mul hC]
  exact (productArcMoment_le_full k p L M hA).trans (ENNReal.ofReal_le_ofReal h)

theorem product_minor8_abs_bound (L M n : ℕ) (hM : 1≤M) (A : Set ℝ)
    {C₀ C₁ C₂ : ℝ≥0∞} (hC₀ : C₀≠⊤) (hC₁ : C₁≠⊤) (hC₂ : C₂≠⊤)
    {ε : ℝ} (hε : ε≤7/200000)
    (h₀ : ordinaryArcMoment 8 72 ((M : ℝ)^L) A≤C₀*ENNReal.ofReal ((M : ℝ)^L)^(63+ε))
    (h₁ : productArcMoment 8 32 L M A≤C₁*ENNReal.ofReal ((M : ℝ)^L)^(24+Endgame.delta8_32+ε))
    (h₂ : productArcMoment 8 34 L M A≤C₂*ENNReal.ofReal ((M : ℝ)^L)^(26+Endgame.delta8_34+ε)) :
    |productArcContribution 8 8 30 L M n A|≤
      MinorArcFinite.positiveConstant8 C₀ C₁ C₂*((M : ℝ)^L)^(30-7/200000 : ℝ) := by
  have hP : 1≤(M : ℝ)^L := one_le_pow₀ (by exact_mod_cast hM)
  have hP' : 1≤ENNReal.ofReal ((M : ℝ)^L) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hP
  have hf : AEMeasurable (absoluteOrdinary 8 ((M : ℝ)^L)) (volume.restrict A) :=
    (continuous_ordinary 8 ((M : ℝ)^L)).norm.aemeasurable.ennreal_ofReal
  have hg : AEMeasurable (absoluteProduct 8 L M) (volume.restrict A) :=
    (continuous_productWeyl 8 L M).norm.aemeasurable.ennreal_ofReal
  have hb := MinorArcFinite.degree8 hf hg hP' ENNReal.ofReal_ne_top hC₀ hC₁ hC₂ hε h₀ h₁ h₂
  exact real_power_bound (MinorArcFinite.positiveConstant8_pos _ _ _).le
    (zero_le_one.trans hP) (by norm_num)
    ((productArcContribution_abs_le_lintegral 8 8 30 L M n A).trans hb.2.1)

theorem product_minor9_abs_bound (L M n : ℕ) (hM : 1≤M) (A : Set ℝ)
    {C₀ C₁ C₂ : ℝ≥0∞} (hC₀ : C₀≠⊤) (hC₁ : C₁≠⊤) (hC₂ : C₂≠⊤)
    {ε : ℝ} (hε : ε≤1/4000)
    (h₀ : ordinaryArcMoment 9 90 ((M : ℝ)^L) A≤C₀*ENNReal.ofReal ((M : ℝ)^L)^(80+ε))
    (h₁ : productArcMoment 9 38 L M A≤C₁*ENNReal.ofReal ((M : ℝ)^L)^(29+Endgame.delta9_38+ε))
    (h₂ : productArcMoment 9 40 L M A≤C₂*ENNReal.ofReal ((M : ℝ)^L)^(31+Endgame.delta9_40+ε)) :
    |productArcContribution 9 11 35 L M n A|≤
      MinorArcFinite.positiveConstant9 C₀ C₁ C₂*((M : ℝ)^L)^(37-1/4000 : ℝ) := by
  have hP : 1≤(M : ℝ)^L := one_le_pow₀ (by exact_mod_cast hM)
  have hP' : 1≤ENNReal.ofReal ((M : ℝ)^L) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hP
  have hf : AEMeasurable (absoluteOrdinary 9 ((M : ℝ)^L)) (volume.restrict A) :=
    (continuous_ordinary 9 ((M : ℝ)^L)).norm.aemeasurable.ennreal_ofReal
  have hg : AEMeasurable (absoluteProduct 9 L M) (volume.restrict A) :=
    (continuous_productWeyl 9 L M).norm.aemeasurable.ennreal_ofReal
  have hb := MinorArcFinite.degree9 hf hg hP' ENNReal.ofReal_ne_top hC₀ hC₁ hC₂ hε h₀ h₁ h₂
  exact real_power_bound (MinorArcFinite.positiveConstant9_pos _ _ _).le
    (zero_le_one.trans hP) (by norm_num)
    ((productArcContribution_abs_le_lintegral 9 11 35 L M n A).trans hb.2.1)

theorem product_minor8_from_admissible
    (h32 : AdmissibleExcess 8 32 Endgame.delta8_32)
    (h34 : AdmissibleExcess 8 34 Endgame.delta8_34) :
    ∃ η : ℝ,0<η ∧ ∀ L : ℕ,1≤(L : ℝ)*η → ∃ C : ℝ,0<C ∧ ∃ P₀ : ℝ,1≤P₀ ∧
      ∀ M : ℕ,1≤M → P₀≤(M : ℝ)^L → ∀ n : ℕ,
        |productArcContribution 8 8 30 L M n (ordinaryMinorRegion 8 ((M : ℝ)^L))|≤
          C*((M : ℝ)^L)^(30-7/200000 : ℝ) := by
  have hr : AdmissibleExponent 8 (2*16) (24+Endgame.delta8_32) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,show (32 : ℝ)-8=24 by norm_num] using h32
  have hs : AdmissibleExponent 8 (2*17) (26+Endgame.delta8_34) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,show (34 : ℝ)-8=26 by norm_num] using h34
  obtain ⟨η,hη,hpair⟩ := product_admissible_pair hr hs epsilon8_pos
  obtain ⟨A,hA,hord⟩ := degree8_ordinary_minor72 epsilon8_pos
  refine ⟨η,hη,?_⟩
  intro L hL
  obtain ⟨B,hB,P₀,hP₀,hprod⟩ := hpair L
  refine ⟨MinorArcFinite.positiveConstant8 (ENNReal.ofReal A) (ENNReal.ofReal B) (ENNReal.ofReal B),
    MinorArcFinite.positiveConstant8_pos _ _ _,P₀,hP₀,?_⟩
  intro M hM hP n
  have hp : 0<(M : ℝ)^L := pow_pos (by exact_mod_cast (show 0<M by omega)) _
  have hb := hprod M hM hP hL
  apply product_minor8_abs_bound L M n hM _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top epsilon8_budget
  · rw [ENNReal.ofReal_rpow_of_pos hp,← ENNReal.ofReal_mul hA.le]
    simpa only [Nat.cast_pow] using hord (M^L) (one_le_pow₀ hM)
  · exact productArcMoment_le_of_bound 8 32 L M hM hB.le Set.diff_subset hb.1
  · exact productArcMoment_le_of_bound 8 34 L M hM hB.le Set.diff_subset hb.2

theorem product_minor9_from_admissible
    (h38 : AdmissibleExcess 9 38 Endgame.delta9_38)
    (h40 : AdmissibleExcess 9 40 Endgame.delta9_40) :
    ∃ η : ℝ,0<η ∧ ∀ L : ℕ,1≤(L : ℝ)*η → ∃ C : ℝ,0<C ∧ ∃ P₀ : ℝ,1≤P₀ ∧
      ∀ M : ℕ,1≤M → P₀≤(M : ℝ)^L → ∀ n : ℕ,
        |productArcContribution 9 11 35 L M n (ordinaryMinorRegion 9 ((M : ℝ)^L))|≤
          C*((M : ℝ)^L)^(37-1/4000 : ℝ) := by
  have hr : AdmissibleExponent 9 (2*19) (29+Endgame.delta9_38) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,show (38 : ℝ)-9=29 by norm_num] using h38
  have hs : AdmissibleExponent 9 (2*20) (31+Endgame.delta9_40) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,show (40 : ℝ)-9=31 by norm_num] using h40
  obtain ⟨η,hη,hpair⟩ := product_admissible_pair hr hs epsilon9_pos
  obtain ⟨A,hA,hord⟩ := degree9_ordinary_minor90 epsilon9_pos
  refine ⟨η,hη,?_⟩
  intro L hL
  obtain ⟨B,hB,P₀,hP₀,hprod⟩ := hpair L
  refine ⟨MinorArcFinite.positiveConstant9 (ENNReal.ofReal A) (ENNReal.ofReal B) (ENNReal.ofReal B),
    MinorArcFinite.positiveConstant9_pos _ _ _,P₀,hP₀,?_⟩
  intro M hM hP n
  have hp : 0<(M : ℝ)^L := pow_pos (by exact_mod_cast (show 0<M by omega)) _
  have hb := hprod M hM hP hL
  apply product_minor9_abs_bound L M n hM _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top epsilon9_budget
  · rw [ENNReal.ofReal_rpow_of_pos hp,← ENNReal.ofReal_mul hA.le]
    simpa only [Nat.cast_pow] using hord (M^L) (one_le_pow₀ hM)
  · exact productArcMoment_le_of_bound 9 38 L M hM hB.le Set.diff_subset hb.1
  · exact productArcMoment_le_of_bound 9 40 L M hM hB.le Set.diff_subset hb.2

#print axioms product_minor8_from_admissible
#print axioms product_minor9_from_admissible
end Waring.EndgameCompletion
