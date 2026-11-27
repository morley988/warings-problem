import Waring.EndgameCompletionProductCutoff

/-!
# Product-box endgame from the exact intended smooth admissibility inputs

This file keeps its remaining assumptions explicit. The analytic positive
core contract is discharged separately by the actual product-box main-term
proof. The only remaining moment inputs in the degree specializations are
the stated VW95 smooth admissible excesses.
-/

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace Waring.EndgameCompletion
open MixedEndgame SmoothMoments

def ProductCoreLowerBound (k u v : ℕ) : Prop :=
  ∀ L : ℕ,1≤L → ∃ c : ℝ,0<c ∧ ∀ᶠ n in atTop,
    c*(productScaleP k L n)^(u+v-k)≤
      productArcContribution k u v L (productScaleM k L n) n
        (ordinaryCore k (productScaleP k L n) (productScaleCutoff k L n))

theorem product_minor_scale_isLittleO (k u v L : ℕ) (hk : 0<k) (hL : 0<L)
    {C P₀ main saving : ℝ} (hsaving : 0<saving)
    (hbound : ∀ M : ℕ,1≤M → P₀≤(M : ℝ)^L → ∀ n : ℕ,
      |productArcContribution k u v L M n (ordinaryMinorRegion k ((M : ℝ)^L))|≤
        C*((M : ℝ)^L)^(main-saving)) :
    (fun n=>productArcContribution k u v L (productScaleM k L n) n
      (ordinaryMinorRegion k (productScaleP k L n)))=o[atTop]
        (fun n=>(productScaleP k L n)^main) := by
  have hP := productScaleP_tendsto k L hk hL
  apply AsymptoticEndgame.power_saving_isLittleO hsaving hP
  apply IsBigO.of_bound C
  filter_upwards [(productScaleM_tendsto k L hk hL).eventually_ge_atTop 1,
    hP.eventually_ge_atTop P₀] with n hm hp
  have hh := hbound (productScaleM k L n) hm hp n
  simpa only [productScaleP,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)] using hh

theorem waringBound_of_product_scale_errors (k u v L : ℕ) (hk : 0<k) (hL : 0<L)
    (hmain : ∃ c : ℝ,0<c ∧ ∀ᶠ n in atTop,
      c*(productScaleP k L n)^(u+v-k)≤
        productArcContribution k u v L (productScaleM k L n) n
          (ordinaryCore k (productScaleP k L n) (productScaleCutoff k L n)))
    (hpruning : (fun n=>productArcContribution k u v L (productScaleM k L n) n
        (ordinaryPruning k (productScaleP k L n) (productScaleCutoff k L n)))=o[atTop]
      (fun n=>(productScaleP k L n)^((u+v-k : ℕ) : ℝ)))
    (hminor : (fun n=>productArcContribution k u v L (productScaleM k L n) n
        (ordinaryMinorRegion k (productScaleP k L n)))=o[atTop]
      (fun n=>(productScaleP k L n)^((u+v-k : ℕ) : ℝ))) :
    WaringBound k (u+v) := by
  obtain ⟨c,hc,hcore⟩ := hmain
  refine waringBound_of_product_two_errors (k := k) (u := u) (v := v) (L := L)
    (main := fun n=>productArcContribution k u v L (productScaleM k L n) n
      (ordinaryCore k (productScaleP k L n) (productScaleCutoff k L n)))
    (productScaleM k L) hc ?_ ?_ ?_ hpruning hminor
  · filter_upwards [(productScaleP_tendsto k L hk hL).eventually_ge_atTop 1] with n hn
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hn) _
  · exact Filter.Eventually.of_forall (fun n=>
      productIntegral_partition k u v L (productScaleM k L n) n
        (ordinary_arc_partition k (productScaleP k L n) (productScaleCutoff k L n)))
  · simpa only [Real.rpow_natCast] using hcore

/-- Conditional only on the explicit core contract and the intended
degree-eight smooth admissible excesses. All ordinary moments and pruning
inputs have been proved and substituted. -/
theorem waring8_from_admissible_and_product_main
    (h32 : AdmissibleExcess 8 32 Endgame.delta8_32)
    (h34 : AdmissibleExcess 8 34 Endgame.delta8_34)
    (hcore : ProductCoreLowerBound 8 8 30) : WaringBound 8 38 := by
  obtain ⟨η,hη,hminor⟩ := product_minor8_from_admissible h32 h34
  obtain ⟨L,hL,hLη⟩ := exists_product_rank hη
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := hminor L hLη
  have hLp : 0<L := by omega
  have hM := (productScaleM_tendsto 8 L (by norm_num) hLp).eventually_ge_atTop 1
  have hP := productScaleP_tendsto 8 L (by norm_num) hLp
  have hκ := productCutoffExponent_facts L hLp
  apply waringBound_of_product_scale_errors 8 8 30 L (by norm_num) hLp (hcore L hL)
  · exact product_pruning8_isLittleO L hκ.1 hκ.2.1 (productScaleM 8 L) hM hP
  · exact product_minor_scale_isLittleO 8 8 30 L (by norm_num) hLp
      (saving := 7/200000) (by norm_num) hbound

/-- Conditional only on the explicit core contract and the intended
degree-nine smooth admissible excesses. -/
theorem waring9_from_admissible_and_product_main
    (h38 : AdmissibleExcess 9 38 Endgame.delta9_38)
    (h40 : AdmissibleExcess 9 40 Endgame.delta9_40)
    (hcore : ProductCoreLowerBound 9 11 35) : WaringBound 9 46 := by
  obtain ⟨η,hη,hminor⟩ := product_minor9_from_admissible h38 h40
  obtain ⟨L,hL,hLη⟩ := exists_product_rank hη
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := hminor L hLη
  have hLp : 0<L := by omega
  have hM := (productScaleM_tendsto 9 L (by norm_num) hLp).eventually_ge_atTop 1
  have hP := productScaleP_tendsto 9 L (by norm_num) hLp
  have hκ := productCutoffExponent_facts L hLp
  apply waringBound_of_product_scale_errors 9 11 35 L (by norm_num) hLp (hcore L hL)
  · exact product_pruning9_isLittleO L hκ.1 hκ.2.1 (productScaleM 9 L) hM hP
  · exact product_minor_scale_isLittleO 9 11 35 L (by norm_num) hLp
      (saving := 1/4000) (by norm_num) hbound

#print axioms waring8_from_admissible_and_product_main
#print axioms waring9_from_admissible_and_product_main
end Waring.EndgameCompletion
