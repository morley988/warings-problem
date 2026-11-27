import WaringSiegel.WSL2Packing
import WaringSiegel.WSL2IdealNorm
import Mathlib.Data.Set.Card

/-!
# WSL2: anisotropic packing for actual fractional ideals

The product of local radii is counted with the correct real/complex
multiplicities. The packing constant is independent of the ideal and of
all ratios between the radii.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def rescaleMixed (R : InfinitePlace K → ℝ) (x : mixedSpace K) : mixedSpace K :=
  (fun w => x.1 w / R w.1, fun w => x.2 w / (R w.1 : ℂ))

theorem rescaleMixed_sub (R : InfinitePlace K → ℝ) (x y : mixedSpace K) :
    rescaleMixed R (x - y) = rescaleMixed R x - rescaleMixed R y := by
  ext w <;> simp only [rescaleMixed, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_div]

theorem rescaleMixed_injective (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w) :
    Function.Injective (rescaleMixed R) := by
  intro x y h
  apply Prod.ext
  · funext w
    have hw := congrArg (fun z : mixedSpace K => z.1 w) h
    change x.1 w / R w.1 = y.1 w / R w.1 at hw
    exact (div_left_inj' (hR w.1).ne').mp hw
  · funext w
    have hw := congrArg (fun z : mixedSpace K => z.2 w) h
    change x.2 w / (R w.1 : ℂ) = y.2 w / (R w.1 : ℂ) at hw
    have hn : (R w.1 : ℂ) ≠ 0 := by exact_mod_cast (hR w.1).ne'
    exact (div_left_inj' hn).mp hw

theorem normAtPlace_rescaleMixed (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w)
    (x : mixedSpace K) (w : InfinitePlace K) :
    normAtPlace w (rescaleMixed R x) = normAtPlace w x / R w := by
  rcases w.isReal_or_isComplex with hr | hc
  · rw [normAtPlace_apply_of_isReal hr, normAtPlace_apply_of_isReal hr]
    simp only [rescaleMixed, norm_div, Real.norm_eq_abs, abs_of_pos (hR w)]
  · rw [normAtPlace_apply_of_isComplex hc, normAtPlace_apply_of_isComplex hc]
    simp only [rescaleMixed, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hR w)]

theorem mixed_norm_le_iff (x : mixedSpace K) (r : ℝ) :
    ‖x‖ ≤ r ↔ ∀ w, normAtPlace w x ≤ r := by
  classical
  rw [norm_eq_sup'_normAtPlace, Finset.sup'_le_iff]
  simp only [Finset.mem_univ, forall_true_left]

theorem normAtPlace_le_mixed_norm (x : mixedSpace K) (w : InfinitePlace K) :
    normAtPlace w x ≤ ‖x‖ := (mixed_norm_le_iff x ‖x‖).mp le_rfl w

theorem mixed_productNorm_le_norm_pow (x : mixedSpace K) :
    NumberField.mixedEmbedding.norm x ≤ ‖x‖ ^ finrank ℚ K := by
  classical
  rw [NumberField.mixedEmbedding.norm_apply,
    ← NumberField.InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro w hw
    exact pow_nonneg (normAtPlace_nonneg w x) _
  · intro w hw
    exact pow_le_pow_left₀ (normAtPlace_nonneg w x) (normAtPlace_le_mixed_norm x w) _

theorem mixed_productNorm_rescale (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w)
    (x : mixedSpace K) :
    NumberField.mixedEmbedding.norm (rescaleMixed R x) =
      NumberField.mixedEmbedding.norm x / ∏ w, R w ^ mult w := by
  classical
  simp only [NumberField.mixedEmbedding.norm_apply, normAtPlace_rescaleMixed R hR,
    div_pow, Finset.prod_div_distrib]

/-- Exact degree-dimensional packing bound, uniform in the fractional ideal,
its translate, the center, and all positive archimedean radii. -/
theorem fractionalIdeal_anisotropic_packing
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (S : Finset K)
    (a : K) (c : mixedSpace K) (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w)
    (hmem : ∀ z ∈ S, z - a ∈ I)
    (hbox : ∀ z ∈ S, ∀ w, normAtPlace w (mixedEmbedding K z - c) ≤ R w) :
    (S.card : ℝ) ≤ (3 : ℝ) ^ finrank ℚ K *
      (1 + (∏ w, R w ^ mult w) / (FractionalIdeal.absNorm I : ℝ)) := by
  classical
  let V : ℝ := ∏ w, R w ^ mult w
  let N : ℝ := FractionalIdeal.absNorm I
  let d : ℕ := finrank ℚ K
  have hV : 0 < V := Finset.prod_pos (fun w _ => pow_pos (hR w) _)
  have hN : 0 < N := fractionalIdeal_absNorm_pos I hI
  have hd : d ≠ 0 := by
    dsimp [d]
    exact ne_of_gt (Module.finrank_pos (R := ℚ) (M := K))
  let δ : ℝ := (N / V) ^ ((d : ℝ)⁻¹)
  have hδ : 0 < δ := Real.rpow_pos_of_pos (div_pos hN hV) _
  have hδpow : δ ^ d = N / V :=
    Real.rpow_inv_natCast_pow (div_nonneg hN.le hV.le) hd
  let f : K → mixedSpace K := fun z => rescaleMixed R (mixedEmbedding K z - c)
  have hf : Function.Injective f := by
    intro x y h
    apply mixedEmbedding_injective
    exact sub_left_injective (rescaleMixed_injective R hR h)
  let T : Finset (mixedSpace K) := S.image f
  have hcard : T.card = S.card := Finset.card_image_of_injective S hf
  have hTbox : ∀ x ∈ T, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    apply (mixed_norm_le_iff _ _).mpr
    intro w
    rw [show f z = rescaleMixed R (mixedEmbedding K z - c) from rfl,
      normAtPlace_rescaleMixed R hR]
    exact (div_le_one (hR w)).mpr (hbox z hz w)
  have hTsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have hzt : z - t ≠ 0 := sub_ne_zero.mpr (fun h => hxy (congrArg f h))
    have hztmem : z - t ∈ I := by
      have hm := (I : Submodule (𝓞 K) K).sub_mem (hmem z hz) (hmem t ht)
      simpa only [sub_sub_sub_cancel_right] using hm
    have hlo := fractionalIdeal_absNorm_le_mixed_norm I hztmem hzt
    have hprod := mixed_productNorm_le_norm_pow
      (rescaleMixed R (mixedEmbedding K (z - t)))
    rw [mixed_productNorm_rescale R hR] at hprod
    have hscaled : f z - f t = rescaleMixed R (mixedEmbedding K (z - t)) := by
      dsimp [f]
      rw [← rescaleMixed_sub, sub_sub_sub_cancel_right, map_sub]
    apply le_of_pow_le_pow_left₀ hd (norm_nonneg _)
    rw [hδpow, hscaled]
    exact (div_le_div_of_nonneg_right hlo hV.le).trans hprod
  have hpack := packing_unit_ball_bound T δ hδ hTbox hTsep
  rw [hcard, NumberField.mixedEmbedding.finrank] at hpack
  change (S.card : ℝ) ≤ 3 ^ d * (1 + 1 / δ ^ d) at hpack
  rw [hδpow, one_div_div] at hpack
  exact hpack

/-- The actual set of fractional-ideal coset points in an archimedean box. -/
def idealBox (I : FractionalIdeal (𝓞 K)⁰ K) (a : K) (c : mixedSpace K)
    (R : InfinitePlace K → ℝ) : Set K :=
  {z | z - a ∈ I ∧ ∀ w, normAtPlace w (mixedEmbedding K z - c) ≤ R w}

theorem idealBox_finite (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (a : K) (c : mixedSpace K) (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w) :
    (idealBox I a c R).Finite := by
  classical
  let B : ℝ := (3 : ℝ) ^ finrank ℚ K *
    (1 + (∏ w, R w ^ mult w) / (FractionalIdeal.absNorm I : ℝ))
  by_contra hinf
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈B⌉₊ + 1)
  have hbound := fractionalIdeal_anisotropic_packing I hI S a c R hR
    (fun z hz => (hS hz).1) (fun z hz => (hS hz).2)
  change (S.card : ℝ) ≤ B at hbound
  have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  rw [hcard, Nat.cast_add, Nat.cast_one] at hbound
  linarith

/-- A bound for the cardinality of the whole actual box, whose finiteness
has been proved rather than assumed. -/
theorem idealBox_ncard_bound (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (a : K) (c : mixedSpace K) (R : InfinitePlace K → ℝ) (hR : ∀ w, 0 < R w) :
    ((idealBox I a c R).ncard : ℝ) ≤ (3 : ℝ) ^ finrank ℚ K *
      (1 + (∏ w, R w ^ mult w) / (FractionalIdeal.absNorm I : ℝ)) := by
  classical
  have hf := idealBox_finite I hI a c R hR
  have h := fractionalIdeal_anisotropic_packing I hI hf.toFinset a c R hR
    (fun z hz => (hf.mem_toFinset.mp hz).1) (fun z hz => (hf.mem_toFinset.mp hz).2)
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact h

end WaringSiegel
