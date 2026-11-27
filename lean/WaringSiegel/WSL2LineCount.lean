import WaringSiegel.WSL2Conductor

/-!
# WSL2: conductor-sensitive close-pair counts

The radii are the minimum of the original box radius and the radius forced
by the error in the affine slope. A zero slope error is handled explicitly.
The constant is independent of all archimedean aspect ratios.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def closePairRadius (θ : mixedSpace K) (γ : K) (R : ℝ)
    (Z : InfinitePlace K → ℝ) (w : InfinitePlace K) : ℝ :=
  if normAtPlace w (θ - mixedEmbedding K γ) = 0 then 2 * R
  else min (2 * R) (2 * Z w / normAtPlace w (θ - mixedEmbedding K γ))

theorem closePairRadius_pos (θ : mixedSpace K) (γ : K) (R : ℝ) (hR : 0 < R)
    (Z : InfinitePlace K → ℝ) (hZ : ∀ w, 0 < Z w) (w : InfinitePlace K) :
    0 < closePairRadius θ γ R Z w := by
  unfold closePairRadius
  split_ifs with hz
  · positivity
  · have hp := lt_of_le_of_ne (normAtPlace_nonneg w (θ - mixedEmbedding K γ)) (Ne.symm hz)
    exact lt_min (by positivity) (div_pos (mul_pos (by norm_num) (hZ w)) hp)

theorem closePairs_line_local_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (θ η : mixedSpace K) (R : ℝ)
    (Z : InfinitePlace K → ℝ) (p r : 𝓞 K × K)
    (hp : p ∈ closePairs I θ η R Z) (hr : r ∈ closePairs I θ η R Z)
    (γ : K) (hline : p.2 = r.2 + γ * ((p.1 : K) - (r.1 : K)))
    (w : InfinitePlace K) :
    normAtPlace w (mixedEmbedding K ((p.1 : K) - (r.1 : K))) ≤
      closePairRadius θ γ R Z w := by
  obtain ⟨hu, he⟩ := closePairs_difference_bounds I θ η R Z p r hp hr w
  have heq : (θ - mixedEmbedding K γ) *
      mixedEmbedding K ((p.1 : K) - (r.1 : K)) =
      θ * mixedEmbedding K ((p.1 : K) - (r.1 : K)) - mixedEmbedding K (p.2 - r.2) := by
    rw [hline]
    simp only [add_sub_cancel_left, map_sub, map_mul]
    ring
  have hmul : normAtPlace w (θ - mixedEmbedding K γ) *
      normAtPlace w (mixedEmbedding K ((p.1 : K) - (r.1 : K))) ≤ 2 * Z w := by
    rw [← map_mul, heq]
    exact he
  unfold closePairRadius
  split_ifs with hz
  · exact hu
  · have hpos := lt_of_le_of_ne (normAtPlace_nonneg w (θ - mixedEmbedding K γ)) (Ne.symm hz)
    exact le_min hu ((le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hmul))

/-- A finite set of actual close pairs on a line satisfies the manuscript's
conductor-sensitive anisotropic bound, with the explicit constant `3^d`. -/
theorem closePairs_line_card_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R : ℝ) (hR : 0 < R)
    (Z : InfinitePlace K → ℝ) (hZ : ∀ w, 0 < Z w)
    (r : 𝓞 K × K) (hr : r ∈ closePairs I θ η R Z)
    (γ : K) (S : Finset (𝓞 K × K))
    (hS : ∀ p ∈ S, p ∈ closePairs I θ η R Z)
    (hline : ∀ p ∈ S, p.2 = r.2 + γ * ((p.1 : K) - (r.1 : K))) :
    (S.card : ℝ) ≤ (3 : ℝ) ^ finrank ℚ K *
      (1 + (∏ w, closePairRadius θ γ R Z w ^ mult w) /
        (Ideal.absNorm (conductorIdeal I γ) : ℝ)) := by
  let J : FractionalIdeal (𝓞 K)⁰ K := conductorIdeal I γ
  have hJ : J ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr (conductorIdeal_ne_zero I hI γ)
  let T : Finset K := S.image (fun p => (p.1 : K))
  have hinj : Set.InjOn (fun p : 𝓞 K × K => (p.1 : K)) S := by
    intro p hp q hq hy
    have hfirst : p.1 = q.1 := RingOfIntegers.coe_injective hy
    have hsecond : p.2 = q.2 := by rw [hline p hp, hline q hq, hfirst]
    exact Prod.ext hfirst hsecond
  have hcard : T.card = S.card := Finset.card_image_iff.mpr hinj
  have hmem : ∀ z ∈ T, z - (r.1 : K) ∈ J := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    have hpJ := closePairs_mem_conductor_coset I p r γ (hS p hp).1 hr.1 (hline p hp)
    have hm := FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ (P := K) hpJ
    simpa only [map_sub, ← RingOfIntegers.coe_eq_algebraMap] using hm
  have hbox : ∀ z ∈ T, ∀ w,
      normAtPlace w (mixedEmbedding K z - mixedEmbedding K (r.1 : K)) ≤
        closePairRadius θ γ R Z w := by
    intro z hz w
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    simpa only [← map_sub] using
      closePairs_line_local_bound I θ η R Z p r (hS p hp) hr γ (hline p hp) w
  have h := fractionalIdeal_anisotropic_packing J hJ T (r.1 : K)
    (mixedEmbedding K (r.1 : K)) (closePairRadius θ γ R Z)
    (closePairRadius_pos θ γ R hR Z hZ) hmem hbox
  rw [hcard] at h
  simpa only [J, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] using h

/-- In the small-volume range, a suitable slope exists and the actual
whole set of close pairs satisfies the conductor-sensitive count. -/
theorem closePairs_finite_and_count
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R : ℝ) (hR : 1 ≤ R)
    (Z : InfinitePlace K → ℝ) (hZ : ∀ w, 0 < Z w)
    (hsmall : (8 * R) ^ finrank ℚ K * (∏ w, Z w ^ mult w) <
      (FractionalIdeal.absNorm I : ℝ))
    (r : 𝓞 K × K) (hr : r ∈ closePairs I θ η R Z) :
    ∃ γ : K, (closePairs I θ η R Z).Finite ∧
      (∀ p ∈ closePairs I θ η R Z, p.2 = r.2 + γ * ((p.1 : K) - (r.1 : K))) ∧
      ((closePairs I θ η R Z).ncard : ℝ) ≤ (3 : ℝ) ^ finrank ℚ K *
        (1 + (∏ w, closePairRadius θ γ R Z w ^ mult w) /
          (Ideal.absNorm (conductorIdeal I γ) : ℝ)) := by
  obtain ⟨γ, hγ⟩ := closePairs_affine_line I θ η R hR Z (fun w => (hZ w).le) hsmall r hr
  let B : ℝ := (3 : ℝ) ^ finrank ℚ K *
    (1 + (∏ w, closePairRadius θ γ R Z w ^ mult w) /
      (Ideal.absNorm (conductorIdeal I γ) : ℝ))
  have hf : (closePairs I θ η R Z).Finite := by
    by_contra hinf
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈B⌉₊ + 1)
    have hb := closePairs_line_card_bound I hI θ η R (by linarith) Z hZ r hr γ S
      (fun p hp => hS hp) (fun p hp => hγ p (hS hp))
    change (S.card : ℝ) ≤ B at hb
    rw [hcard, Nat.cast_add, Nat.cast_one] at hb
    linarith [Nat.le_ceil B]
  refine ⟨γ, hf, hγ, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact closePairs_line_card_bound I hI θ η R (by linarith) Z hZ r hr γ hf.toFinset
    (fun p hp => hf.mem_toFinset.mp hp) (fun p hp => hγ p (hf.mem_toFinset.mp hp))

end WaringSiegel
