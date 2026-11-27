import Waring.EndgameCompletionLocalPositive

/-! # Positive actual prime Euler factors, uniform in the target integer -/

noncomputable section
open scoped BigOperators
open Filter Topology
namespace Waring.EndgameCompletion
open LocalSolubility

def productLocalFactor (k u v L : ℕ) (n : ℤ) (p : ℕ) : ℂ :=
  ∑' j : ℕ,productSingularCoefficient k u v L n (p^j)

theorem productLocalFactor_tendsto {p : ℕ} [NeZero p] (hp : p.Prime)
    (k u v L : ℕ) (n : ℤ)
    (hsum : Summable (fun q=>‖productSingularCoefficient k u v L n q‖)) :
    Tendsto (fun r=>fullProductSingularCoefficient (p^r) k u v L n)
      atTop (𝓝 (productLocalFactor k u v L n p)) := by
  have hs := hsum.of_norm.comp_injective (Nat.pow_right_injective hp.one_lt)
  have ht := (tendsto_add_atTop_iff_nat 1).mpr hs.hasSum.tendsto_sum_nat
  simpa only [Function.comp_apply,productSingularCoefficient_prime_partial_sum hp,productLocalFactor] using ht

theorem productLocalFactor_real_tendsto {p : ℕ} [NeZero p] (hp : p.Prime)
    (k u v L : ℕ) (n : ℤ)
    (hsum : Summable (fun q=>‖productSingularCoefficient k u v (L+1) n q‖)) :
    Tendsto (fun r=>productLocalDensity (p^r) k u v L n)
      atTop (𝓝 (productLocalFactor k u v (L+1) n p).re) := by
  have ht := (Complex.continuous_re.tendsto _).comp
    (productLocalFactor_tendsto hp k u v (L+1) n hsum)
  simpa only [fullProductSingularCoefficient_eq_density,Complex.ofReal_re] using ht

theorem productLocalFactor_im_eq_zero {p : ℕ} [NeZero p] (hp : p.Prime)
    (k u v L : ℕ) (n : ℤ)
    (hsum : Summable (fun q=>‖productSingularCoefficient k u v (L+1) n q‖)) :
    (productLocalFactor k u v (L+1) n p).im=0 := by
  have ht := (Complex.continuous_im.tendsto _).comp
    (productLocalFactor_tendsto hp k u v (L+1) n hsum)
  have hh : Tendsto (fun _ : ℕ=>(0 : ℝ)) atTop
      (𝓝 (productLocalFactor k u v (L+1) n p).im) := by
    simpa only [fullProductSingularCoefficient_eq_density,Complex.ofReal_im] using ht
  exact tendsto_nhds_unique hh tendsto_const_nhds

theorem degree8_productLocalFactor_lower {p : ℕ} [NeZero p] (hp : p.Prime)
    (L : ℕ) (n : ℤ) :
    primeDensityLower p 38 (L*30) (localDepth8 p)≤
      (productLocalFactor 8 8 30 (L+1) n p).re := by
  have ht := productLocalFactor_real_tendsto hp 8 8 30 L n
    (degree8_productSingularCoefficient_summable L n)
  have ht' : Tendsto (fun r=>productLocalDensity (p^(r+localDepth8 p)) 8 8 30 L n)
      atTop (𝓝 (productLocalFactor 8 8 30 (L+1) n p).re) :=
    (tendsto_add_atTop_iff_nat (localDepth8 p)).mpr ht
  exact ge_of_tendsto' ht' (fun r=>degree8_productLocalDensity_lower hp L r n)

theorem degree9_productLocalFactor_lower {p : ℕ} [NeZero p] (hp : p.Prime)
    (L : ℕ) (n : ℤ) :
    primeDensityLower p 46 (L*35) (localDepth9 p)≤
      (productLocalFactor 9 11 35 (L+1) n p).re := by
  have ht := productLocalFactor_real_tendsto hp 9 11 35 L n
    (degree9_productSingularCoefficient_summable L n)
  have ht' : Tendsto (fun r=>productLocalDensity (p^(r+localDepth9 p)) 9 11 35 L n)
      atTop (𝓝 (productLocalFactor 9 11 35 (L+1) n p).re) :=
    (tendsto_add_atTop_iff_nat (localDepth9 p)).mpr ht
  exact ge_of_tendsto' ht' (fun r=>degree9_productLocalDensity_lower hp L r n)

theorem degree8_productLocalFactor_pos {p : ℕ} [NeZero p] (hp : p.Prime)
    (L : ℕ) (n : ℤ) : 0<(productLocalFactor 8 8 30 (L+1) n p).re :=
  (primeDensityLower_pos hp.pos _ _ _).trans_le (degree8_productLocalFactor_lower hp L n)

theorem degree9_productLocalFactor_pos {p : ℕ} [NeZero p] (hp : p.Prime)
    (L : ℕ) (n : ℤ) : 0<(productLocalFactor 9 11 35 (L+1) n p).re :=
  (primeDensityLower_pos hp.pos _ _ _).trans_le (degree9_productLocalFactor_lower hp L n)

#print axioms degree8_productLocalFactor_lower
#print axioms degree9_productLocalFactor_pos
end Waring.EndgameCompletion
