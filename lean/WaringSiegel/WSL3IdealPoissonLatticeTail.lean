import WaringSiegel.WSL3IdealPoissonCubicBound

/-!
# Arbitrary rapid nonzero-dual tails from the actual ideal norm

The extra decay factor is a power of the anisotropic radius volume divided
by the ideal norm. It holds on every actual nonzero fractional-ideal point,
and sums uniformly over all ideal shapes and local radius ratios.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 250000
variable {K : Type*} [Field K] [NumberField K]

def latticePowerDecay (m : ℕ) (R : InfinitePlace K → ℝ) (z : K) : ℝ :=
  ∏ w, 1/(1+normAtPlace w (mixedEmbedding K z)/R w)^m

def latticePlaceProductBase (R : InfinitePlace K → ℝ) (z : K) : ℝ :=
  ∏ w, (1+normAtPlace w (mixedEmbedding K z)/R w)

theorem latticePowerDecay_eq (m : ℕ) (R : InfinitePlace K → ℝ) (z : K) :
    latticePowerDecay m R z = 1/(latticePlaceProductBase R z)^m := by
  simp only [latticePowerDecay,latticePlaceProductBase,Finset.prod_div_distrib,
    Finset.prod_const_one,Finset.prod_pow]

theorem latticePowerDecay_base (R : InfinitePlace K → ℝ) (z : K) :
    latticePowerDecay (finrank ℚ K+2) R z = latticeProductDecay R 0 z := by
  simp only [latticePowerDecay,latticeProductDecay,sub_zero]

theorem latticePlaceProductBase_pos (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w) (z : K) :
    0 < latticePlaceProductBase R z := by
  apply Finset.prod_pos
  intro w hw
  have hn := normAtPlace_nonneg w (mixedEmbedding K z)
  have hr := hR w
  positivity

theorem latticePlaceProductBase_ge_norm (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w) (z : K) :
    ‖rescaleMixed R (mixedEmbedding K z)‖ ≤ latticePlaceProductBase R z := by
  let b : InfinitePlace K → ℝ := fun w => 1+normAtPlace w (mixedEmbedding K z)/R w
  have hb (w : InfinitePlace K) : 1 ≤ b w := by
    have h := div_nonneg (normAtPlace_nonneg w (mixedEmbedding K z)) (hR w).le
    dsimp only [b]
    linarith
  apply (mixed_norm_le_iff _ _).mpr
  intro w
  rw [normAtPlace_rescaleMixed R hR]
  calc
    _ ≤ b w := by dsimp only [b]; linarith
    _ = ∏ v : InfinitePlace K, if v=w then b w else 1 := by simp
    _ ≤ latticePlaceProductBase R z := by
      apply Finset.prod_le_prod
      · intro v hv
        split_ifs <;> linarith [hb w]
      · intro v hv
        split_ifs with h
        · subst v; exact le_rfl
        · exact hb v

/-- Actual algebraic norm separation at every nonzero ideal point. -/
theorem latticePlaceProductBase_norm_separation
    (I : FractionalIdeal (𝓞 K)⁰ K) (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w)
    (ξ : I) (hξ : (ξ:K) ≠ 0) :
    (FractionalIdeal.absNorm I:ℝ)/(∏ w, (R w)^mult w) ≤
      (latticePlaceProductBase R (ξ:K))^(finrank ℚ K) := by
  have hN := fractionalIdeal_absNorm_le_mixed_norm I ξ.property hξ
  have hV : 0 < ∏ w : InfinitePlace K, (R w)^mult w :=
    Finset.prod_pos (fun w _ => pow_pos (hR w) _)
  calc
    _ ≤ NumberField.mixedEmbedding.norm (mixedEmbedding K (ξ:K))/(∏ w, (R w)^mult w) :=
      div_le_div_of_nonneg_right hN hV.le
    _ = NumberField.mixedEmbedding.norm (rescaleMixed R (mixedEmbedding K (ξ:K))) :=
      (mixed_productNorm_rescale R hR _).symm
    _ ≤ ‖rescaleMixed R (mixedEmbedding K (ξ:K))‖^(finrank ℚ K) := mixed_productNorm_le_norm_pow _
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) (latticePlaceProductBase_ge_norm R hR (ξ:K)) _

/-- Each extra block of d powers supplies one factor radius-volume/ideal-norm. -/
theorem latticePowerDecay_nonzero_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w)
    (N : ℕ) (ξ : I) (hξ : (ξ:K) ≠ 0) :
    latticePowerDecay (finrank ℚ K*N+(finrank ℚ K+2)) R (ξ:K) ≤
      ((∏ w, (R w)^mult w)/(FractionalIdeal.absNorm I:ℝ))^N * latticeProductDecay R 0 (ξ:K) := by
  let A := latticePlaceProductBase R (ξ:K)
  let V : ℝ := ∏ w : InfinitePlace K, (R w)^mult w
  let q : ℝ := FractionalIdeal.absNorm I
  have hA : 0 < A := latticePlaceProductBase_pos R hR (ξ:K)
  have hV : 0 < V := Finset.prod_pos (fun w _ => pow_pos (hR w) _)
  have hq : 0 < q := fractionalIdeal_absNorm_pos I hI
  have hsep := latticePlaceProductBase_norm_separation I R hR ξ hξ
  have hp := pow_le_pow_left₀ (div_nonneg hq.le hV.le) hsep N
  rw [← pow_mul] at hp
  have hinv : 1/A^(finrank ℚ K*N) ≤ (V/q)^N := by
    calc
      _ ≤ 1/(q/V)^N := one_div_le_one_div_of_le (pow_pos (div_pos hq hV) N) hp
      _ = _ := by rw [one_div,← inv_pow,inv_div]
  rw [← latticePowerDecay_base,latticePowerDecay_eq,latticePowerDecay_eq,pow_add]
  have hh := mul_le_mul_of_nonneg_right hinv (le_of_lt (one_div_pos.mpr (pow_pos hA (finrank ℚ K+2))))
  simpa only [div_eq_mul_inv,mul_inv,one_mul,V,q,A] using hh

/-- Actual nonzero dual series with every desired power of the anisotropic
radius-to-ideal-norm ratio, including proved absolute summability. -/
theorem fractionalIdeal_nonzero_power_decay
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w)
    (N : ℕ) :
    Summable (fun ξ : {ξ : I // (ξ:K) ≠ 0} =>
      latticePowerDecay (finrank ℚ K*N+(finrank ℚ K+2)) R ((ξ:I):K)) ∧
    (∑' ξ : {ξ : I // (ξ:K) ≠ 0}, latticePowerDecay (finrank ℚ K*N+(finrank ℚ K+2)) R ((ξ:I):K)) ≤
      2*(3:ℝ)^(finrank ℚ K)*((∏ w, (R w)^mult w)/(FractionalIdeal.absNorm I:ℝ))^N *
        (1+(∏ w, (R w)^mult w)/(FractionalIdeal.absNorm I:ℝ)) := by
  obtain ⟨hs,hb⟩ := fractionalIdeal_product_decay_zero I hI R hR
  have hs0 : Summable (fun ξ : {ξ : I // (ξ:K) ≠ 0} => latticeProductDecay R 0 ((ξ:I):K)) :=
    hs.subtype {ξ : I | (ξ:K) ≠ 0}
  have hb0 : (∑' ξ : {ξ : I // (ξ:K) ≠ 0}, latticeProductDecay R 0 ((ξ:I):K)) ≤
      (∑' ξ : I, latticeProductDecay R 0 (ξ:K)) := by
    exact Summable.tsum_subtype_le (fun ξ : I => latticeProductDecay R 0 (ξ:K))
      {ξ : I | (ξ:K) ≠ 0} (fun ξ => latticeProductDecay_nonneg R hR 0 (ξ:K)) hs
  let E : ℝ := ((∏ w, (R w)^mult w)/(FractionalIdeal.absNorm I:ℝ))^N
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact pow_nonneg (div_nonneg (Finset.prod_nonneg (fun w _ => pow_nonneg (hR w).le _))
      (fractionalIdeal_absNorm_pos I hI).le) N
  have hsnew : Summable (fun ξ : {ξ : I // (ξ:K) ≠ 0} =>
      latticePowerDecay (finrank ℚ K*N+(finrank ℚ K+2)) R ((ξ:I):K)) := by
    apply Summable.of_nonneg_of_le _ _ (hs0.mul_left E)
    · intro ξ
      rw [latticePowerDecay_eq]
      exact (one_div_pos.mpr (pow_pos (latticePlaceProductBase_pos R hR _) _)).le
    · intro ξ
      exact latticePowerDecay_nonzero_bound I hI R hR N ξ.val ξ.property
  refine ⟨hsnew, ?_⟩
  have hpoint (ξ : {ξ : I // (ξ:K) ≠ 0}) :
      latticePowerDecay (finrank ℚ K*N+(finrank ℚ K+2)) R ((ξ:I):K) ≤
        E*latticeProductDecay R 0 ((ξ:I):K) :=
    latticePowerDecay_nonzero_bound I hI R hR N ξ.val ξ.property
  have hh := hsnew.tsum_le_tsum hpoint (hs0.mul_left E)
  rw [tsum_mul_left] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left (hb0.trans hb) hE)).trans_eq (by dsimp only [E]; ring)

#print axioms latticePowerDecay_nonzero_bound
#print axioms fractionalIdeal_nonzero_power_decay
end WaringSiegel.WSL3Poisson
