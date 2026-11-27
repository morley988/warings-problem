import Waring.EndgameCompletionCriterionMinor
import Waring.EndgameCompletionAdmissibleTargets

/-!
# The Waring targets from the exact strict moment criteria

All major arcs, pruning, ordinary minor moments, and representation counting
are discharged. The two admissible smooth moments may be any actual proved
exponents satisfying the displayed strict rational inequalities.
-/

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace Waring.EndgameCompletion
open SmoothMoments

theorem waring8_from_admissible_excess_criterion {d32 d34 : ℝ}
    (h32 : AdmissibleExcess 8 32 d32) (h34 : AdmissibleExcess 8 34 d34)
    (hcrit : d32+7*d34<1) : WaringBound 8 38 := by
  obtain ⟨η,hη,hminor⟩ := product_minor8_from_criterion h32 h34 hcrit
  obtain ⟨L,hL,hLη⟩ := exists_product_rank hη
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := hminor L hLη
  have hLp : 0<L := by omega
  have hM := (productScaleM_tendsto 8 L (by norm_num) hLp).eventually_ge_atTop 1
  have hP := productScaleP_tendsto 8 L (by norm_num) hLp
  have hκ := productCutoffExponent_facts L hLp
  apply waringBound_of_product_scale_errors 8 8 30 L (by norm_num) hLp
    (degree8_productCoreLowerBound L hL)
  · exact product_pruning8_isLittleO L hκ.1 hκ.2.1 (productScaleM 8 L) hM hP
  · exact product_minor_scale_isLittleO 8 8 30 L (by norm_num) hLp
      (criterionSaving8_pos hcrit) hbound

theorem waring9_from_admissible_excess_criterion {d38 d40 : ℝ}
    (h38 : AdmissibleExcess 9 38 d38) (h40 : AdmissibleExcess 9 40 d40)
    (hcrit : 5*d38+74*d40<11) : WaringBound 9 46 := by
  obtain ⟨η,hη,hminor⟩ := product_minor9_from_criterion h38 h40 hcrit
  obtain ⟨L,hL,hLη⟩ := exists_product_rank hη
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := hminor L hLη
  have hLp : 0<L := by omega
  have hM := (productScaleM_tendsto 9 L (by norm_num) hLp).eventually_ge_atTop 1
  have hP := productScaleP_tendsto 9 L (by norm_num) hLp
  have hκ := productCutoffExponent_facts L hLp
  apply waringBound_of_product_scale_errors 9 11 35 L (by norm_num) hLp
    (degree9_productCoreLowerBound L hL)
  · exact product_pruning9_isLittleO L hκ.1 hκ.2.1 (productScaleM 9 L) hM hP
  · exact product_minor_scale_isLittleO 9 11 35 L (by norm_num) hLp
      (criterionSaving9_pos hcrit) hbound

theorem waring8_from_admissible_exponent_criterion {lam32 lam34 : ℝ}
    (h32 : AdmissibleExponent 8 32 lam32) (h34 : AdmissibleExponent 8 34 lam34)
    (hcrit : lam32+7*lam34<207) : WaringBound 8 38 := by
  have h32' : AdmissibleExcess 8 32 (lam32-24) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,
      show (32 : ℝ)-8+(lam32-24)=lam32 by ring] using h32
  have h34' : AdmissibleExcess 8 34 (lam34-26) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,
      show (34 : ℝ)-8+(lam34-26)=lam34 by ring] using h34
  exact waring8_from_admissible_excess_criterion h32' h34' (by linarith)

theorem waring9_from_admissible_exponent_criterion {lam38 lam40 : ℝ}
    (h38 : AdmissibleExponent 9 38 lam38) (h40 : AdmissibleExponent 9 40 lam40)
    (hcrit : 5*lam38+74*lam40<2450) : WaringBound 9 46 := by
  have h38' : AdmissibleExcess 9 38 (lam38-29) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,
      show (38 : ℝ)-9+(lam38-29)=lam38 by ring] using h38
  have h40' : AdmissibleExcess 9 40 (lam40-31) := by
    simpa only [AdmissibleExcess,Nat.cast_ofNat,
      show (40 : ℝ)-9+(lam40-31)=lam40 by ring] using h40
  exact waring9_from_admissible_excess_criterion h38' h40' (by linarith)

theorem waring8_from_rational_admissible_exponents {lam32 lam34 : ℚ}
    (h32 : AdmissibleExponent 8 32 (lam32 : ℝ))
    (h34 : AdmissibleExponent 8 34 (lam34 : ℝ))
    (hcrit : lam32+7*lam34<207) : WaringBound 8 38 := by
  apply waring8_from_admissible_exponent_criterion h32 h34
  exact_mod_cast hcrit

theorem waring9_from_rational_admissible_exponents {lam38 lam40 : ℚ}
    (h38 : AdmissibleExponent 9 38 (lam38 : ℝ))
    (h40 : AdmissibleExponent 9 40 (lam40 : ℝ))
    (hcrit : 5*lam38+74*lam40<2450) : WaringBound 9 46 := by
  apply waring9_from_admissible_exponent_criterion h38 h40
  exact_mod_cast hcrit

#print axioms waring8_from_admissible_excess_criterion
#print axioms waring9_from_admissible_excess_criterion
#print axioms waring8_from_rational_admissible_exponents
#print axioms waring9_from_rational_admissible_exponents
end Waring.EndgameCompletion
