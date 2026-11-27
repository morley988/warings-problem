import WaringSiegel.WSL2AnisotropicPacking

/-! # WSL2: actual algebraic-integer archimedean box counts -/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem integer_box_card_bound (S : Finset (𝓞 K)) (P : ℝ) (hP : 1 ≤ P)
    (hbox : ∀ x ∈ S, ∀ w : InfinitePlace K, w (x : K) ≤ P) :
    (S.card : ℝ) ≤ 2 * (3 : ℝ) ^ finrank ℚ K * P ^ finrank ℚ K := by
  let T : Finset K := S.image (fun x : 𝓞 K => (x : K))
  have hinj : Function.Injective (fun x : 𝓞 K => (x : K)) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hcard : T.card = S.card := Finset.card_image_of_injective S hinj
  have h := fractionalIdeal_anisotropic_packing (1 : FractionalIdeal (𝓞 K)⁰ K)
    one_ne_zero T 0 0 (fun _ => P) (fun _ => by linarith) (by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      simpa only [sub_zero] using FractionalIdeal.coe_mem_one (𝓞 K)⁰ x) (by
      intro z hz w
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      simpa only [sub_zero, normAtPlace_apply] using hbox x hx w)
  rw [hcard, FractionalIdeal.absNorm_one, Rat.cast_one, div_one,
    Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq] at h
  have hpow : 1 ≤ P ^ finrank ℚ K := one_le_pow₀ hP
  calc
    _ ≤ (3 : ℝ) ^ finrank ℚ K * (1 + P ^ finrank ℚ K) := h
    _ ≤ 2 * (3 : ℝ) ^ finrank ℚ K * P ^ finrank ℚ K := by
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (finrank ℚ K)]

end WaringSiegel
