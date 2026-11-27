import Waring.EndgameCompletionProductMinor

/-!
# Product minor arcs for arbitrary admissible excesses

The strict Holder inequalities, rather than the particular published decimal
values, are the exact hypotheses needed by the endgame. Half the available
saving is assigned to the common moment epsilon and half is retained.
-/

noncomputable section
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology
namespace Waring.EndgameCompletion
open MixedEndgame SmoothMoments

def criterionSaving8 (d32 d34 : ℝ) : ℝ := (1-d32-7*d34)/18
def criterionSaving9 (d38 d40 : ℝ) : ℝ := (11-5*d38-74*d40)/180

theorem criterionSaving8_pos {d32 d34 : ℝ} (h : d32+7*d34<1) :
    0<criterionSaving8 d32 d34 := by unfold criterionSaving8; linarith

theorem criterionSaving9_pos {d38 d40 : ℝ} (h : 5*d38+74*d40<11) :
    0<criterionSaving9 d38 d40 := by unfold criterionSaving9; linarith

theorem minor8_criterion_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F g : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hg : AEMeasurable g μ)
    {P C₀ C₁ C₂ : ℝ≥0∞} (hP : 1≤P) (hPtop : P≠⊤)
    (hC₀ : C₀≠⊤) (hC₁ : C₁≠⊤) (hC₂ : C₂≠⊤) (d32 d34 : ℝ)
    (h₀ : (∫⁻ x,F x^(72 : ℕ) ∂μ)≤C₀*P^(63+criterionSaving8 d32 d34))
    (h₁ : (∫⁻ x,g x^(32 : ℕ) ∂μ)≤C₁*P^(24+d32+criterionSaving8 d32 d34))
    (h₂ : (∫⁻ x,g x^(34 : ℕ) ∂μ)≤C₂*P^(26+d34+criterionSaving8 d32 d34)) :
    (∫⁻ x,F x^(8 : ℕ)*g x^(30 : ℕ) ∂μ)≤
      ENNReal.ofReal (MinorArcFinite.positiveConstant8 C₀ C₁ C₂)*
        P^(30-criterionSaving8 d32 d34) := by
  have hP₀ : P≠0 := ne_of_gt (zero_lt_one.trans_le hP)
  have h := MinorArc.three_moment_bounds hP₀ hPtop
    (a := (1/9 : ℝ)) (b := (1/9 : ℝ)) (c := (7/9 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) h₀ h₁ h₂
  have he : (63+criterionSaving8 d32 d34)*(1/9)+
      (24+d32+criterionSaving8 d32 d34)*(1/9)+
      (26+d34+criterionSaving8 d32 d34)*(7/9)=30-criterionSaving8 d32 d34 := by
    unfold criterionSaving8
    ring
  rw [he] at h
  have hc := MinorArcFinite.le_ofReal_positiveConstant
    (MinorArcFinite.weighted8_ne_top hC₀ hC₁ hC₂)
  exact (Holder.minor8 hF hg).trans (h.trans (mul_le_mul_right' hc _))

theorem minor9_criterion_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F g : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hg : AEMeasurable g μ)
    {P C₀ C₁ C₂ : ℝ≥0∞} (hP : 1≤P) (hPtop : P≠⊤)
    (hC₀ : C₀≠⊤) (hC₁ : C₁≠⊤) (hC₂ : C₂≠⊤) (d38 d40 : ℝ)
    (h₀ : (∫⁻ x,F x^(90 : ℕ) ∂μ)≤C₀*P^(80+criterionSaving9 d38 d40))
    (h₁ : (∫⁻ x,g x^(38 : ℕ) ∂μ)≤C₁*P^(29+d38+criterionSaving9 d38 d40))
    (h₂ : (∫⁻ x,g x^(40 : ℕ) ∂μ)≤C₂*P^(31+d40+criterionSaving9 d38 d40)) :
    (∫⁻ x,F x^(11 : ℕ)*g x^(35 : ℕ) ∂μ)≤
      ENNReal.ofReal (MinorArcFinite.positiveConstant9 C₀ C₁ C₂)*
        P^(37-criterionSaving9 d38 d40) := by
  have hP₀ : P≠0 := ne_of_gt (zero_lt_one.trans_le hP)
  have h := MinorArc.three_moment_bounds hP₀ hPtop
    (a := (11/90 : ℝ)) (b := (5/90 : ℝ)) (c := (74/90 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) h₀ h₁ h₂
  have he : (80+criterionSaving9 d38 d40)*(11/90)+
      (29+d38+criterionSaving9 d38 d40)*(5/90)+
      (31+d40+criterionSaving9 d38 d40)*(74/90)=37-criterionSaving9 d38 d40 := by
    unfold criterionSaving9
    ring
  rw [he] at h
  have hc := MinorArcFinite.le_ofReal_positiveConstant
    (MinorArcFinite.weighted9_ne_top hC₀ hC₁ hC₂)
  exact (Holder.minor9 hF hg).trans (h.trans (mul_le_mul_right' hc _))

theorem real_power_bound_of_pos {x C P exponent : ℝ} (hC : 0≤C) (hP : 0<P)
    (h : ENNReal.ofReal |x|≤ENNReal.ofReal C*ENNReal.ofReal P^exponent) :
    |x|≤C*P^exponent := by
  rw [ENNReal.ofReal_rpow_of_pos hP,← ENNReal.ofReal_mul hC] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (Real.rpow_nonneg hP.le _))).mp h

theorem product_minor8_criterion_abs (L M n : ℕ) (hM : 1≤M) (A : Set ℝ)
    {C₀ C₁ C₂ : ℝ≥0∞} (hC₀ : C₀≠⊤) (hC₁ : C₁≠⊤) (hC₂ : C₂≠⊤) (d32 d34 : ℝ)
    (h₀ : ordinaryArcMoment 8 72 ((M : ℝ)^L) A≤
      C₀*ENNReal.ofReal ((M : ℝ)^L)^(63+criterionSaving8 d32 d34))
    (h₁ : productArcMoment 8 32 L M A≤
      C₁*ENNReal.ofReal ((M : ℝ)^L)^(24+d32+criterionSaving8 d32 d34))
    (h₂ : productArcMoment 8 34 L M A≤
      C₂*ENNReal.ofReal ((M : ℝ)^L)^(26+d34+criterionSaving8 d32 d34)) :
    |productArcContribution 8 8 30 L M n A|≤
      MinorArcFinite.positiveConstant8 C₀ C₁ C₂*((M : ℝ)^L)^(30-criterionSaving8 d32 d34) := by
  have hP : 1≤(M : ℝ)^L := one_le_pow₀ (by exact_mod_cast hM)
  have hP' : 1≤ENNReal.ofReal ((M : ℝ)^L) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hP
  have hf : AEMeasurable (absoluteOrdinary 8 ((M : ℝ)^L)) (volume.restrict A) :=
    (continuous_ordinary 8 ((M : ℝ)^L)).norm.aemeasurable.ennreal_ofReal
  have hg : AEMeasurable (absoluteProduct 8 L M) (volume.restrict A) :=
    (continuous_productWeyl 8 L M).norm.aemeasurable.ennreal_ofReal
  have hb := minor8_criterion_lintegral hf hg hP' ENNReal.ofReal_ne_top hC₀ hC₁ hC₂
    d32 d34 h₀ h₁ h₂
  exact real_power_bound_of_pos (MinorArcFinite.positiveConstant8_pos _ _ _).le
    (zero_lt_one.trans_le hP)
    ((productArcContribution_abs_le_lintegral 8 8 30 L M n A).trans hb)

theorem product_minor9_criterion_abs (L M n : ℕ) (hM : 1≤M) (A : Set ℝ)
    {C₀ C₁ C₂ : ℝ≥0∞} (hC₀ : C₀≠⊤) (hC₁ : C₁≠⊤) (hC₂ : C₂≠⊤) (d38 d40 : ℝ)
    (h₀ : ordinaryArcMoment 9 90 ((M : ℝ)^L) A≤
      C₀*ENNReal.ofReal ((M : ℝ)^L)^(80+criterionSaving9 d38 d40))
    (h₁ : productArcMoment 9 38 L M A≤
      C₁*ENNReal.ofReal ((M : ℝ)^L)^(29+d38+criterionSaving9 d38 d40))
    (h₂ : productArcMoment 9 40 L M A≤
      C₂*ENNReal.ofReal ((M : ℝ)^L)^(31+d40+criterionSaving9 d38 d40)) :
    |productArcContribution 9 11 35 L M n A|≤
      MinorArcFinite.positiveConstant9 C₀ C₁ C₂*((M : ℝ)^L)^(37-criterionSaving9 d38 d40) := by
  have hP : 1≤(M : ℝ)^L := one_le_pow₀ (by exact_mod_cast hM)
  have hP' : 1≤ENNReal.ofReal ((M : ℝ)^L) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hP
  have hf : AEMeasurable (absoluteOrdinary 9 ((M : ℝ)^L)) (volume.restrict A) :=
    (continuous_ordinary 9 ((M : ℝ)^L)).norm.aemeasurable.ennreal_ofReal
  have hg : AEMeasurable (absoluteProduct 9 L M) (volume.restrict A) :=
    (continuous_productWeyl 9 L M).norm.aemeasurable.ennreal_ofReal
  have hb := minor9_criterion_lintegral hf hg hP' ENNReal.ofReal_ne_top hC₀ hC₁ hC₂
    d38 d40 h₀ h₁ h₂
  exact real_power_bound_of_pos (MinorArcFinite.positiveConstant9_pos _ _ _).le
    (zero_lt_one.trans_le hP)
    ((productArcContribution_abs_le_lintegral 9 11 35 L M n A).trans hb)

theorem product_minor8_from_criterion {d32 d34 : ℝ}
    (h32 : AdmissibleExcess 8 32 d32) (h34 : AdmissibleExcess 8 34 d34)
    (hcrit : d32+7*d34<1) :
    ∃ η : ℝ,0<η ∧ ∀ L : ℕ,1≤(L : ℝ)*η → ∃ C : ℝ,0<C ∧ ∃ P₀ : ℝ,1≤P₀ ∧
      ∀ M : ℕ,1≤M → P₀≤(M : ℝ)^L → ∀ n : ℕ,
        |productArcContribution 8 8 30 L M n (ordinaryMinorRegion 8 ((M : ℝ)^L))|≤
          C*((M : ℝ)^L)^(30-criterionSaving8 d32 d34) := by
  have hε := criterionSaving8_pos hcrit
  have hr : AdmissibleExponent 8 (2*16) (24+d32) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,show (32 : ℝ)-8=24 by norm_num] using h32
  have hs : AdmissibleExponent 8 (2*17) (26+d34) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,show (34 : ℝ)-8=26 by norm_num] using h34
  obtain ⟨η,hη,hpair⟩ := product_admissible_pair hr hs hε
  obtain ⟨A,hA,hord⟩ := degree8_ordinary_minor72 hε
  refine ⟨η,hη,?_⟩
  intro L hL
  obtain ⟨B,hB,P₀,hP₀,hprod⟩ := hpair L
  refine ⟨MinorArcFinite.positiveConstant8 (ENNReal.ofReal A) (ENNReal.ofReal B) (ENNReal.ofReal B),
    MinorArcFinite.positiveConstant8_pos _ _ _,P₀,hP₀,?_⟩
  intro M hM hP n
  have hp : 0<(M : ℝ)^L := pow_pos (by exact_mod_cast (show 0<M by omega)) _
  have hb := hprod M hM hP hL
  apply product_minor8_criterion_abs L M n hM _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top d32 d34
  · rw [ENNReal.ofReal_rpow_of_pos hp,← ENNReal.ofReal_mul hA.le]
    simpa only [Nat.cast_pow] using hord (M^L) (one_le_pow₀ hM)
  · exact productArcMoment_le_of_bound 8 32 L M hM hB.le Set.diff_subset hb.1
  · exact productArcMoment_le_of_bound 8 34 L M hM hB.le Set.diff_subset hb.2

theorem product_minor9_from_criterion {d38 d40 : ℝ}
    (h38 : AdmissibleExcess 9 38 d38) (h40 : AdmissibleExcess 9 40 d40)
    (hcrit : 5*d38+74*d40<11) :
    ∃ η : ℝ,0<η ∧ ∀ L : ℕ,1≤(L : ℝ)*η → ∃ C : ℝ,0<C ∧ ∃ P₀ : ℝ,1≤P₀ ∧
      ∀ M : ℕ,1≤M → P₀≤(M : ℝ)^L → ∀ n : ℕ,
        |productArcContribution 9 11 35 L M n (ordinaryMinorRegion 9 ((M : ℝ)^L))|≤
          C*((M : ℝ)^L)^(37-criterionSaving9 d38 d40) := by
  have hε := criterionSaving9_pos hcrit
  have hr : AdmissibleExponent 9 (2*19) (29+d38) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,show (38 : ℝ)-9=29 by norm_num] using h38
  have hs : AdmissibleExponent 9 (2*20) (31+d40) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,show (40 : ℝ)-9=31 by norm_num] using h40
  obtain ⟨η,hη,hpair⟩ := product_admissible_pair hr hs hε
  obtain ⟨A,hA,hord⟩ := degree9_ordinary_minor90 hε
  refine ⟨η,hη,?_⟩
  intro L hL
  obtain ⟨B,hB,P₀,hP₀,hprod⟩ := hpair L
  refine ⟨MinorArcFinite.positiveConstant9 (ENNReal.ofReal A) (ENNReal.ofReal B) (ENNReal.ofReal B),
    MinorArcFinite.positiveConstant9_pos _ _ _,P₀,hP₀,?_⟩
  intro M hM hP n
  have hp : 0<(M : ℝ)^L := pow_pos (by exact_mod_cast (show 0<M by omega)) _
  have hb := hprod M hM hP hL
  apply product_minor9_criterion_abs L M n hM _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top d38 d40
  · rw [ENNReal.ofReal_rpow_of_pos hp,← ENNReal.ofReal_mul hA.le]
    simpa only [Nat.cast_pow] using hord (M^L) (one_le_pow₀ hM)
  · exact productArcMoment_le_of_bound 9 38 L M hM hB.le Set.diff_subset hb.1
  · exact productArcMoment_le_of_bound 9 40 L M hM hB.le Set.diff_subset hb.2

#print axioms product_minor8_from_criterion
#print axioms product_minor9_from_criterion
end Waring.EndgameCompletion
