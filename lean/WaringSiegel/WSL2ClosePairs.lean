import WaringSiegel.WSL2AnisotropicPacking
import WaringSiegel.AffineLine

/-!
# WSL2: small-volume close pairs on an actual affine field line

The determinant argument is carried out in the actual mixed archimedean
space. Both the determinant's fractional-ideal membership and its local
norm bounds are proved. The statement applies in particular to the inverse
different, but is uniform in any nonzero fractional ideal.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem normAtPlace_sub_le (w : InfinitePlace K) (x y : mixedSpace K) :
    normAtPlace w (x - y) ≤ normAtPlace w x + normAtPlace w y := by
  simpa only [sub_eq_add_neg, normAtPlace_neg] using normAtPlace_add_le w x (-y)

theorem mixed_productNorm_le_scaled_radii
    (x : mixedSpace K) (C : ℝ) (hC : 0 ≤ C)
    (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 ≤ R w)
    (hx : ∀ w, normAtPlace w x ≤ C * R w) :
    NumberField.mixedEmbedding.norm x ≤
      C ^ finrank ℚ K * ∏ w, R w ^ mult w := by
  calc
    _ ≤ ∏ w, (C * R w) ^ mult w := by
      rw [NumberField.mixedEmbedding.norm_apply]
      exact Finset.prod_le_prod (fun w _ => pow_nonneg (normAtPlace_nonneg w x) _)
        (fun w _ => pow_le_pow_left₀ (normAtPlace_nonneg w x) (hx w) _)
    _ = _ := by
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        InfinitePlace.sum_mult_eq]

theorem normAtPlace_determinant_le
    (w : InfinitePlace K) (θ u₁ b₁ u₂ b₂ : mixedSpace K) (U Z : ℝ)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z)
    (hu₁ : normAtPlace w u₁ ≤ U) (hu₂ : normAtPlace w u₂ ≤ U)
    (he₁ : normAtPlace w (θ * u₁ - b₁) ≤ Z)
    (he₂ : normAtPlace w (θ * u₂ - b₂) ≤ Z) :
    normAtPlace w (b₁ * u₂ - b₂ * u₁) ≤ 2 * U * Z := by
  have heq : b₁ * u₂ - b₂ * u₁ =
      (θ * u₂ - b₂) * u₁ - (θ * u₁ - b₁) * u₂ := by ring
  rw [heq]
  calc
    _ ≤ normAtPlace w ((θ * u₂ - b₂) * u₁) +
        normAtPlace w ((θ * u₁ - b₁) * u₂) := normAtPlace_sub_le _ _ _
    _ = normAtPlace w (θ * u₂ - b₂) * normAtPlace w u₁ +
        normAtPlace w (θ * u₁ - b₁) * normAtPlace w u₂ := by rw [map_mul, map_mul]
    _ ≤ Z * U + Z * U := add_le_add
      (mul_le_mul he₂ hu₁ (normAtPlace_nonneg _ _) hZ)
      (mul_le_mul he₁ hu₂ (normAtPlace_nonneg _ _) hZ)
    _ = _ := by ring

def closePairs (I : FractionalIdeal (𝓞 K)⁰ K)
    (θ η : mixedSpace K) (R : ℝ) (Z : InfinitePlace K → ℝ) : Set (𝓞 K × K) :=
  {p | p.2 ∈ I ∧
    (∀ w, normAtPlace w (mixedEmbedding K (p.1 : K)) ≤ R) ∧
    ∀ w, normAtPlace w (θ * mixedEmbedding K (p.1 : K) + η -
      mixedEmbedding K p.2) ≤ Z w}

def closePairDet (p q r : 𝓞 K × K) : K :=
  (p.2 - r.2) * ((q.1 : K) - (r.1 : K)) -
    (q.2 - r.2) * ((p.1 : K) - (r.1 : K))

theorem closePairDet_mem (I : FractionalIdeal (𝓞 K)⁰ K)
    (p q r : 𝓞 K × K) (hp : p.2 ∈ I) (hq : q.2 ∈ I) (hr : r.2 ∈ I) :
    closePairDet p q r ∈ I := by
  have h₁ := (I : Submodule (𝓞 K) K).smul_mem (q.1 - r.1)
    ((I : Submodule (𝓞 K) K).sub_mem hp hr)
  have h₂ := (I : Submodule (𝓞 K) K).smul_mem (p.1 - r.1)
    ((I : Submodule (𝓞 K) K).sub_mem hq hr)
  have h := (I : Submodule (𝓞 K) K).sub_mem h₁ h₂
  simpa only [closePairDet, Algebra.smul_def, map_sub,
    ← RingOfIntegers.coe_eq_algebraMap, mul_comm] using h

theorem closePairs_difference_bounds
    (I : FractionalIdeal (𝓞 K)⁰ K) (θ η : mixedSpace K) (R : ℝ)
    (Z : InfinitePlace K → ℝ) (p q : 𝓞 K × K)
    (hp : p ∈ closePairs I θ η R Z) (hq : q ∈ closePairs I θ η R Z)
    (w : InfinitePlace K) :
    normAtPlace w (mixedEmbedding K ((p.1 : K) - (q.1 : K))) ≤ 2 * R ∧
    normAtPlace w (θ * mixedEmbedding K ((p.1 : K) - (q.1 : K)) -
      mixedEmbedding K (p.2 - q.2)) ≤ 2 * Z w := by
  constructor
  · rw [map_sub]
    exact (normAtPlace_sub_le _ _ _).trans (by linarith [hp.2.1 w, hq.2.1 w])
  · have heq : θ * mixedEmbedding K ((p.1 : K) - (q.1 : K)) -
        mixedEmbedding K (p.2 - q.2) =
        (θ * mixedEmbedding K (p.1 : K) + η - mixedEmbedding K p.2) -
        (θ * mixedEmbedding K (q.1 : K) + η - mixedEmbedding K q.2) := by
      simp only [map_sub]
      ring
    rw [heq]
    exact (normAtPlace_sub_le _ _ _).trans (by linarith [hp.2.2 w, hq.2.2 w])

/-- The exact local determinant estimate used by the manuscript. -/
theorem closePairDet_local_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (θ η : mixedSpace K) (R : ℝ) (hR : 0 ≤ R)
    (Z : InfinitePlace K → ℝ) (hZ : ∀ w, 0 ≤ Z w)
    (p q r : 𝓞 K × K)
    (hp : p ∈ closePairs I θ η R Z) (hq : q ∈ closePairs I θ η R Z)
    (hr : r ∈ closePairs I θ η R Z) (w : InfinitePlace K) :
    normAtPlace w (mixedEmbedding K (closePairDet p q r)) ≤ 8 * R * Z w := by
  obtain ⟨hu₁, he₁⟩ := closePairs_difference_bounds I θ η R Z p r hp hr w
  obtain ⟨hu₂, he₂⟩ := closePairs_difference_bounds I θ η R Z q r hq hr w
  have h := normAtPlace_determinant_le w θ
    (mixedEmbedding K ((p.1 : K) - (r.1 : K))) (mixedEmbedding K (p.2 - r.2))
    (mixedEmbedding K ((q.1 : K) - (r.1 : K))) (mixedEmbedding K (q.2 - r.2))
    (2 * R) (2 * Z w) (by positivity) (mul_nonneg (by norm_num) (hZ w)) hu₁ hu₂ he₁ he₂
  simpa only [closePairDet, map_sub, map_mul, show 2 * (2 * R) * (2 * Z w) =
    8 * R * Z w by ring] using h

theorem closePairDet_eq_zero
    (I : FractionalIdeal (𝓞 K)⁰ K) (θ η : mixedSpace K) (R : ℝ) (hR : 0 ≤ R)
    (Z : InfinitePlace K → ℝ) (hZ : ∀ w, 0 ≤ Z w)
    (hsmall : (8 * R) ^ finrank ℚ K * (∏ w, Z w ^ mult w) <
      (FractionalIdeal.absNorm I : ℝ))
    (p q r : 𝓞 K × K)
    (hp : p ∈ closePairs I θ η R Z) (hq : q ∈ closePairs I θ η R Z)
    (hr : r ∈ closePairs I θ η R Z) : closePairDet p q r = 0 := by
  by_contra hn
  have hlo := fractionalIdeal_absNorm_le_mixed_norm I
    (closePairDet_mem I p q r hp.1 hq.1 hr.1) hn
  have hhi := mixed_productNorm_le_scaled_radii (mixedEmbedding K (closePairDet p q r))
    (8 * R) (by positivity) Z hZ (closePairDet_local_bound I θ η R hR Z hZ p q r hp hq hr)
  exact (not_le_of_gt hsmall) (hlo.trans hhi)

/-- In the same small-volume range two close pairs with the same integer
coordinate are identical. Thus the affine line is never forced to be vertical. -/
theorem closePairs_first_injective
    (I : FractionalIdeal (𝓞 K)⁰ K) (θ η : mixedSpace K) (R : ℝ) (hR : 1 ≤ R)
    (Z : InfinitePlace K → ℝ) (hZ : ∀ w, 0 ≤ Z w)
    (hsmall : (8 * R) ^ finrank ℚ K * (∏ w, Z w ^ mult w) <
      (FractionalIdeal.absNorm I : ℝ))
    (p q : 𝓞 K × K) (hp : p ∈ closePairs I θ η R Z)
    (hq : q ∈ closePairs I θ η R Z) (hy : p.1 = q.1) : p = q := by
  have ha : p.2 = q.2 := by
    by_contra hn
    have hlo := fractionalIdeal_absNorm_le_mixed_norm I
      ((I : Submodule (𝓞 K) K).sub_mem hp.1 hq.1) (sub_ne_zero.mpr hn)
    have hlocal : ∀ w, normAtPlace w (mixedEmbedding K (p.2 - q.2)) ≤ (8 * R) * Z w := by
      intro w
      have hh := (closePairs_difference_bounds I θ η R Z p q hp hq w).2
      rw [hy, sub_self, map_zero, mul_zero, zero_sub, normAtPlace_neg] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ 8 * R) (hZ w))
    have hhi := mixed_productNorm_le_scaled_radii (mixedEmbedding K (p.2 - q.2))
      (8 * R) (by positivity) Z hZ hlocal
    exact (not_le_of_gt hsmall) (hlo.trans hhi)
  exact Prod.ext hy ha

/-- All actual close pairs lie on one affine `K`-line under the explicit
norm-volume threshold. No determinant-vanishing assumption remains. -/
theorem closePairs_affine_line
    (I : FractionalIdeal (𝓞 K)⁰ K) (θ η : mixedSpace K) (R : ℝ) (hR : 1 ≤ R)
    (Z : InfinitePlace K → ℝ) (hZ : ∀ w, 0 ≤ Z w)
    (hsmall : (8 * R) ^ finrank ℚ K * (∏ w, Z w ^ mult w) <
      (FractionalIdeal.absNorm I : ℝ))
    (r : 𝓞 K × K) (hr : r ∈ closePairs I θ η R Z) :
    ∃ γ : K, ∀ p ∈ closePairs I θ η R Z,
      p.2 = r.2 + γ * ((p.1 : K) - (r.1 : K)) := by
  by_cases hn : ∃ q ∈ closePairs I θ η R Z, q.1 ≠ r.1
  · obtain ⟨q, hq, hqr⟩ := hn
    have hy : (q.1 : K) ≠ (r.1 : K) := by exact_mod_cast hqr
    let S : Set (K × K) := (fun p : 𝓞 K × K => ((p.1 : K), p.2)) '' closePairs I θ η R Z
    obtain ⟨γ, hγ⟩ := affine_line_of_determinants S (r.1 : K) r.2 (q.1 : K) q.2 hy (by
      rintro t ⟨p, hp, rfl⟩
      exact closePairDet_eq_zero I θ η R (by linarith) Z hZ hsmall p q r hp hq hr)
    exact ⟨γ, fun p hp => hγ _ ⟨p, hp, rfl⟩⟩
  · refine ⟨0, ?_⟩
    intro p hp
    have hy : p.1 = r.1 := by by_contra h; exact hn ⟨p, hp, h⟩
    have heq := closePairs_first_injective I θ η R hR Z hZ hsmall p r hp hr hy
    simp only [heq, zero_mul, add_zero]

end WaringSiegel
