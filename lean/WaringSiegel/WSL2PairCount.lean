import WaringSiegel.WSL2LineCount
import WaringSiegel.WSL2IntegerBox

/-! # WSL2: unconditional close-pair counts, with no small-volume hypothesis -/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem closePairs_fiber_card_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R : ℝ)
    (Z : InfinitePlace K → ℝ) (hZ : ∀ w, 0 < Z w)
    (S : Finset (𝓞 K × K)) (hS : ∀ p ∈ S, p ∈ closePairs I θ η R Z)
    (y : 𝓞 K) :
    ((S.filter (fun p => p.1 = y)).card : ℝ) ≤ (3 : ℝ) ^ finrank ℚ K *
      (1 + (∏ w, Z w ^ mult w) / (FractionalIdeal.absNorm I : ℝ)) := by
  let F := S.filter (fun p => p.1 = y)
  let T : Finset K := F.image Prod.snd
  have hinj : Set.InjOn (Prod.snd : 𝓞 K × K → K) F := by
    intro p hp q hq ha
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) ha
  have hcard : T.card = F.card := Finset.card_image_iff.mpr hinj
  have hmem : ∀ z ∈ T, z - 0 ∈ I := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    simpa only [sub_zero] using (hS p (Finset.mem_filter.mp hp).1).1
  have hbox : ∀ z ∈ T, ∀ w,
      normAtPlace w (mixedEmbedding K z - (θ * mixedEmbedding K (y : K) + η)) ≤ Z w := by
    intro z hz w
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    have he := (hS p (Finset.mem_filter.mp hp).1).2.2 w
    rw [(Finset.mem_filter.mp hp).2] at he
    rwa [← neg_sub, normAtPlace_neg]
  have h := fractionalIdeal_anisotropic_packing I hI T 0
    (θ * mixedEmbedding K (y : K) + η) Z hZ hmem hbox
  rw [hcard] at h
  exact h

theorem closePairs_trivial_card_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R : ℝ) (hR : 1 ≤ R)
    (Z : InfinitePlace K → ℝ) (hZ : ∀ w, 0 < Z w)
    (S : Finset (𝓞 K × K)) (hS : ∀ p ∈ S, p ∈ closePairs I θ η R Z) :
    (S.card : ℝ) ≤ (2 * (3 : ℝ) ^ finrank ℚ K * R ^ finrank ℚ K) *
      ((3 : ℝ) ^ finrank ℚ K *
        (1 + (∏ w, Z w ^ mult w) / (FractionalIdeal.absNorm I : ℝ))) := by
  let Y := S.image Prod.fst
  let B : ℝ := (3 : ℝ) ^ finrank ℚ K *
    (1 + (∏ w, Z w ^ mult w) / (FractionalIdeal.absNorm I : ℝ))
  have hB : 0 ≤ B := by
    have hnorm := (fractionalIdeal_absNorm_pos I hI).le
    have hprod : 0 ≤ ∏ w, Z w ^ mult w := Finset.prod_nonneg (fun w _ => (pow_pos (hZ w) _).le)
    dsimp [B]
    positivity
  have hY := integer_box_card_bound Y R hR (by
    intro y hy w
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    simpa only [normAtPlace_apply] using (hS p hp).2.1 w)
  have hsum : (S.card : ℝ) = ∑ y ∈ Y, ((S.filter (fun p => p.1 = y)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image Prod.fst S
  calc
    _ = ∑ y ∈ Y, ((S.filter (fun p => p.1 = y)).card : ℝ) := hsum
    _ ≤ ∑ y ∈ Y, B := Finset.sum_le_sum (fun y _ => closePairs_fiber_card_bound I hI θ η R Z hZ S hS y)
    _ = (Y.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (3 : ℝ) ^ finrank ℚ K * R ^ finrank ℚ K) * B :=
      mul_le_mul_of_nonneg_right hY hB

theorem closePairs_finite
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R : ℝ) (hR : 1 ≤ R)
    (Z : InfinitePlace K → ℝ) (hZ : ∀ w, 0 < Z w) :
    (closePairs I θ η R Z).Finite := by
  let B : ℝ := (2 * (3 : ℝ) ^ finrank ℚ K * R ^ finrank ℚ K) *
    ((3 : ℝ) ^ finrank ℚ K *
      (1 + (∏ w, Z w ^ mult w) / (FractionalIdeal.absNorm I : ℝ)))
  by_contra hinf
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈B⌉₊ + 1)
  have hb := closePairs_trivial_card_bound I hI θ η R hR Z hZ S (fun p hp => hS hp)
  change (S.card : ℝ) ≤ B at hb
  rw [hcard, Nat.cast_add, Nat.cast_one] at hb
  linarith [Nat.le_ceil B]

theorem closePairs_trivial_ncard_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R : ℝ) (hR : 1 ≤ R)
    (Z : InfinitePlace K → ℝ) (hZ : ∀ w, 0 < Z w) :
    ((closePairs I θ η R Z).ncard : ℝ) ≤
      (2 * (3 : ℝ) ^ finrank ℚ K * R ^ finrank ℚ K) *
      ((3 : ℝ) ^ finrank ℚ K *
        (1 + (∏ w, Z w ^ mult w) / (FractionalIdeal.absNorm I : ℝ))) := by
  have hf := closePairs_finite I hI θ η R hR Z hZ
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact closePairs_trivial_card_bound I hI θ η R hR Z hZ hf.toFinset
    (fun p hp => hf.mem_toFinset.mp hp)

end WaringSiegel
