import Waring.EndgameCompletionProductMomentBounds
import Waring.EndgameCompletionQuantitativePruning

/-! # Actual quantitative mixed pruning for product-box smooth weights -/

noncomputable section
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology
namespace Waring.EndgameCompletion
open MixedEndgame Pruning

theorem product_pruning8_abs_bound (L M n : ℕ) (hM : 1≤M)
    {W Cf Cg : ℝ} (hW : 0<W) (hCf : 0<Cf) (hCg : 0<Cg)
    {A : Set ℝ} (hA : A⊆Set.Ioc 0 1)
    (hF : ordinaryArcMoment 8 12 ((M : ℝ)^L) A≤
      ENNReal.ofReal (Cf*((M : ℝ)^L)^4*W^(-(1/16 : ℝ))))
    (hg : productMoment 8 90 L M≤Cg*((M : ℝ)^L)^82) :
    |productArcContribution 8 8 30 L M n A|≤
      (Cf^(2/3 : ℝ)*Cg^(1/3 : ℝ))*((M : ℝ)^L)^(30 : ℝ)*W^(-(1/24 : ℝ)) := by
  have hp : 0<(M : ℝ)^L := pow_pos (by exact_mod_cast (show 0<M by omega)) _
  have hg90 := (productArcMoment_le_full 8 90 L M hA).trans (ENNReal.ofReal_le_ofReal hg)
  have hf : AEMeasurable (absoluteOrdinary 8 ((M : ℝ)^L)) (volume.restrict A) :=
    (continuous_ordinary 8 ((M : ℝ)^L)).norm.aemeasurable.ennreal_ofReal
  have hgm : AEMeasurable (absoluteProduct 8 L M) (volume.restrict A) :=
    (continuous_productWeyl 8 L M).norm.aemeasurable.ennreal_ofReal
  have hh := Holder.pruning8 hf hgm
  have hb : ENNReal.ofReal |productArcContribution 8 8 30 L M n A|≤
      ENNReal.ofReal (Cf*((M : ℝ)^L)^4*W^(-(1/16 : ℝ)))^(2/3 : ℝ)*
      ENNReal.ofReal (Cg*((M : ℝ)^L)^82)^(1/3 : ℝ) :=
    ((productArcContribution_abs_le_lintegral 8 8 30 L M n A).trans hh).trans
      (mul_le_mul' (ENNReal.rpow_le_rpow hF (by norm_num))
        (ENNReal.rpow_le_rpow hg90 (by norm_num)))
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity),pruning8_exponent_identity hp hW hCf.le hCg.le] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

theorem product_pruning8_quantitative (L : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ M : ℕ,1≤M → ∀ N : ℕ,1≤N → (N : ℝ)≤(M : ℝ)^L → ∀ n : ℕ,
      |productArcContribution 8 8 30 L M n (ordinaryPruning 8 ((M : ℝ)^L) N)|≤
        C*((M : ℝ)^L)^(30+ε)*(N : ℝ)^(-(1/24 : ℝ)) := by
  obtain ⟨Cf,hCf,hF⟩ := degree8_ordinary_pruning12_quantitative
  obtain ⟨Cg,hCg,hg⟩ := degree8_product90_bound L (show 0<3*ε by positivity)
  refine ⟨Cf^(2/3 : ℝ)*Cg^(1/3 : ℝ),by positivity,?_⟩
  intro M hM N hN hNP n
  let P : ℝ := (M : ℝ)^L
  have hP : 1≤P := one_le_pow₀ (by exact_mod_cast hM)
  have hp : 0<P := zero_lt_one.trans_le hP
  have hnp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hg' : productMoment 8 90 L M≤(Cg*P^(3*ε))*P^82 := by
    convert hg M hM using 1
    rw [← Real.rpow_natCast,mul_assoc,← Real.rpow_add hp]
    congr 2
    ring
  have hb := product_pruning8_abs_bound L M n hM hnp hCf
    (show 0<Cg*P^(3*ε) by positivity) (ordinaryPruning_subset 8 P N)
    (hF P hP N hN hNP) hg'
  have hid : (Cf^(2/3 : ℝ)*(Cg*P^(3*ε))^(1/3 : ℝ))*P^(30 : ℝ)*(N : ℝ)^(-(1/24 : ℝ))=
      (Cf^(2/3 : ℝ)*Cg^(1/3 : ℝ))*P^(30+ε)*(N : ℝ)^(-(1/24 : ℝ)) := by
    rw [Real.mul_rpow hCg.le (Real.rpow_nonneg hp.le _),← Real.rpow_mul hp.le,
      show 3*ε*(1/3 : ℝ)=ε by ring,Real.rpow_add hp]
    ring
  exact hb.trans_eq hid

theorem product_pruning9_quantitative :
    ∃ C : ℝ,0<C ∧ ∀ L M : ℕ,1≤M → ∀ N : ℕ,1≤N → (N : ℝ)≤(M : ℝ)^L → ∀ n : ℕ,
      |productArcContribution 9 11 35 L M n (ordinaryPruning 9 ((M : ℝ)^L) N)|≤
        C*((M : ℝ)^L)^(37 : ℝ)*(N : ℝ)^(-(1/18 : ℝ)) := by
  obtain ⟨C,hC,hF⟩ := degree9_ordinary_pruning11_quantitative
  refine ⟨C,hC,?_⟩
  intro L M hM N hN hNP n
  let P : ℝ := (M : ℝ)^L
  let A := ordinaryPruning 9 P N
  have hP : 1≤P := one_le_pow₀ (by exact_mod_cast hM)
  have hp := zero_lt_one.trans_le hP
  have hpoint (α : ℝ) : absoluteProduct 9 L M α^35≤ENNReal.ofReal (P^35) := by
    rw [ENNReal.ofReal_pow hp.le]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (norm_productWeyl_le 9 L M α)) _
  have hh : (∫⁻ α,absoluteOrdinary 9 P α^11*absoluteProduct 9 L M α^35 ∂volume.restrict A)≤
      ordinaryArcMoment 9 11 P A*ENNReal.ofReal (P^35) := by
    calc
      _ ≤ ∫⁻ α,absoluteOrdinary 9 P α^11*ENNReal.ofReal (P^35) ∂volume.restrict A :=
        lintegral_mono (fun α=>mul_le_mul_left' (hpoint α) _)
      _ = _ := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
  have hb := ((productArcContribution_abs_le_lintegral 9 11 35 L M n A).trans hh).trans
    (mul_le_mul_right' (hF P hP N hN hNP) (ENNReal.ofReal (P^35)))
  rw [← ENNReal.ofReal_mul (by positivity)] at hb
  have hid : (C*P^2*(N : ℝ)^(-(1/18 : ℝ)))*P^35=
      C*P^(37 : ℝ)*(N : ℝ)^(-(1/18 : ℝ)) := by norm_num; ring
  rw [hid] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

#print axioms product_pruning8_quantitative
#print axioms product_pruning9_quantitative
end Waring.EndgameCompletion
