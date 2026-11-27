import WaringSiegel.WSL3PoissonMixedLongThinCount
import WaringSiegel.WSL3PoissonTraceSchwartz

/-!
# Original long-thin polynomial tails from actual Gaussian Poisson

Polynomial annulus counts turn the actual Gaussian identity into the
convergent polynomial kernel needed for smooth linear Poisson estimates.
The exact major factor survives this passage.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped BigOperators Classical NumberField nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def originalLongThinRadius (θ : mixedSpace K) (P H : ℝ) (p : inverseDifferent K × 𝓞 K) : ℝ :=
  max (‖mixedEmbedding K (p.2:K)‖/(P*H))
    (P*‖mixedEmbedding K (p.1:K)+θ*mixedEmbedding K (p.2:K)‖)

def originalLongThinRadialDecay (θ : mixedSpace K) (P H : ℝ)
    (p : inverseDifferent K × 𝓞 K) : ℝ :=
  1/(1+originalLongThinRadius θ P H p)^(2*finrank ℚ K+2)

theorem originalLongThinRadius_nonneg (θ : mixedSpace K) (P H : ℝ)
    (hP : 0 ≤ P) (hH : 0 ≤ H) (p : inverseDifferent K × 𝓞 K) :
    0 ≤ originalLongThinRadius θ P H p :=
  le_trans (div_nonneg (norm_nonneg _) (mul_nonneg hP hH)) (le_max_left _ _)

theorem originalLongThinRadialDecay_finite_bound (θ : mixedSpace K) (P H : ℝ)
    (hP : 0 < P) (hH : 0 < H) (S : Finset (inverseDifferent K × 𝓞 K)) :
    (∑ p ∈ S, originalLongThinRadialDecay θ P H p) ≤
      2*(originalGaussianBoxFactor K * (∑' p, longThinOriginalGaussian θ P H p)) := by
  have hPH := mul_pos hP hH
  apply WSL2.finite_annular_decay_bound S (originalLongThinRadius θ P H)
    (fun p hp => originalLongThinRadius_nonneg θ P H hP.le hH.le p)
    (2*finrank ℚ K)
    (originalGaussianBoxFactor K * (∑' p, longThinOriginalGaussian θ P H p))
    (mul_nonneg originalGaussianBoxFactor_pos.le (tsum_nonneg (fun _ => (Real.exp_pos _).le)))
  intro n
  let T := S.filter (fun p => ⌊originalLongThinRadius θ P H p⌋₊=n)
  let u : ℝ := (n:ℝ)+1
  have hu : 1 ≤ u := by dsimp [u]; have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hrad : ∀ p ∈ T, originalLongThinRadius θ P H p ≤ u := by
    intro p hp
    have hf := (Finset.mem_filter.mp hp).2
    have h := Nat.lt_floor_add_one (originalLongThinRadius θ P H p)
    rw [hf] at h
    exact h.le
  have hb := originalThinBox_enlarged_card_le_gaussian θ P H u hP hH hu T
    (by
      intro p hp
      apply (le_div_iff₀ hP).mpr
      have he := (le_max_right _ _).trans (hrad p hp)
      simpa only [mul_comm] using he)
    (by
      intro p hp
      exact (div_le_iff₀ hPH).mp ((le_max_left _ _).trans (hrad p hp)))
  exact hb.trans_eq (by ring)

/-- The full original radial series is absolutely convergent, with no arc premise. -/
theorem originalLongThinRadialDecay_summable_bound (θ : mixedSpace K) (P H : ℝ)
    (hP : 0 < P) (hH : 0 < H) :
    Summable (originalLongThinRadialDecay θ P H) ∧
      (∑' p, originalLongThinRadialDecay θ P H p) ≤
        2*(originalGaussianBoxFactor K * (∑' p, longThinOriginalGaussian θ P H p)) := by
  have hnonneg (p : inverseDifferent K × 𝓞 K) : 0 ≤ originalLongThinRadialDecay θ P H p := by
    have h := originalLongThinRadius_nonneg θ P H hP.le hH.le p
    unfold originalLongThinRadialDecay
    positivity
  have hb := originalLongThinRadialDecay_finite_bound θ P H hP hH
  have hs := summable_of_sum_le hnonneg hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

/-- Arbitrary product decay is dominated by radial decay in the literal mixed norm. -/
theorem archimedeanProductDecay_le_radial (m : ℕ) (x : mixedSpace K) :
    archimedeanProductDecay m x ≤ 1/(1+‖x‖)^m := by
  obtain ⟨w, hw, he⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (InfinitePlace K)).Nonempty)
    (fun v => normAtPlace v x)
  have hden : (1+‖x‖)^m ≤ ∏ v : InfinitePlace K, (1+normAtPlace v x)^m := by
    rw [norm_eq_sup'_normAtPlace, he]
    have hfac (v : InfinitePlace K) : 1 ≤ (1+normAtPlace v x)^m := by
      have hn := normAtPlace_nonneg v x
      exact one_le_pow₀ (by linarith)
    have herase : 1 ≤ ∏ v ∈ Finset.univ.erase w, (1+normAtPlace v x)^m := by
      calc
        _ = ∏ _v ∈ Finset.univ.erase w, (1:ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun v _ => hfac v)
    calc
      _ = (1+normAtPlace w x)^m * 1 := by ring
      _ ≤ (1+normAtPlace w x)^m * (∏ v ∈ Finset.univ.erase w, (1+normAtPlace v x)^m) :=
        mul_le_mul_of_nonneg_left herase (zero_le_one.trans (hfac w))
      _ = _ := Finset.mul_prod_erase Finset.univ (fun v : InfinitePlace K => (1+normAtPlace v x)^m) hw
  unfold archimedeanProductDecay
  rw [Finset.prod_div_distrib, Finset.prod_const_one]
  exact one_div_le_one_div_of_le (by positivity) hden

def originalLongThinDomain (P H : ℝ) : Set (inverseDifferent K × 𝓞 K) :=
  {p | ‖mixedEmbedding K (p.2:K)‖ ≤ P*H}

def originalLongThinProductDecay (θ : mixedSpace K) (P : ℝ)
    (p : inverseDifferent K × 𝓞 K) : ℝ :=
  archimedeanProductDecay (2*finrank ℚ K+2)
    (P • (mixedEmbedding K (p.1:K)+θ*mixedEmbedding K (p.2:K)))

theorem originalLongThinProductDecay_le_radial (θ : mixedSpace K) (P H : ℝ)
    (hP : 0 < P) (hH : 0 < H) (p : originalLongThinDomain (K:=K) P H) :
    originalLongThinProductDecay θ P p ≤
      (2:ℝ)^(2*finrank ℚ K+2) * originalLongThinRadialDecay θ P H p := by
  let e := P*‖mixedEmbedding K (p.1.1:K)+θ*mixedEmbedding K (p.1.2:K)‖
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hv : ‖mixedEmbedding K (p.1.2:K)‖/(P*H) ≤ 1 :=
    (div_le_one (mul_pos hP hH)).mpr p.property
  have hr : 1+originalLongThinRadius θ P H p ≤ 2*(1+e) := by
    have hmax : originalLongThinRadius θ P H p ≤ 1+e :=
      max_le (hv.trans (by linarith)) (by dsimp [e]; linarith)
    linarith
  have hrpos : 0 < 1+originalLongThinRadius θ P H p := by
    have h := originalLongThinRadius_nonneg θ P H hP.le hH.le p
    positivity
  have hp := pow_le_pow_left₀ hrpos.le hr (2*finrank ℚ K+2)
  rw [mul_pow] at hp
  calc
    _ ≤ 1/(1+e)^(2*finrank ℚ K+2) := by
      simpa only [originalLongThinProductDecay, _root_.norm_smul, Real.norm_eq_abs,
        abs_of_pos hP, e] using archimedeanProductDecay_le_radial (2*finrank ℚ K+2)
          (P • (mixedEmbedding K (p.1.1:K)+θ*mixedEmbedding K (p.1.2:K)))
    _ ≤ _ := by
      unfold originalLongThinRadialDecay
      rw [mul_one_div]
      exact (div_le_div_iff₀ (pow_pos (by positivity : 0 < 1+e) _) (pow_pos hrpos _)).mpr
        (by simpa only [one_mul] using hp)

/-- The full original polynomial Fourier kernel is bounded by the genuine Gaussian. -/
theorem originalLongThinProductDecay_summable_bound (θ : mixedSpace K) (P H : ℝ)
    (hP : 0 < P) (hH : 0 < H) :
    Summable (fun p : originalLongThinDomain (K:=K) P H => originalLongThinProductDecay θ P p) ∧
      (∑' p : originalLongThinDomain (K:=K) P H, originalLongThinProductDecay θ P p) ≤
        (2:ℝ)^(2*finrank ℚ K+2) *
          (2*(originalGaussianBoxFactor K * (∑' p, longThinOriginalGaussian θ P H p))) := by
  obtain ⟨hs, hb⟩ := originalLongThinRadialDecay_summable_bound θ P H hP hH
  have hsub := hs.subtype (originalLongThinDomain (K:=K) P H)
  have hsm := hsub.mul_left ((2:ℝ)^(2*finrank ℚ K+2))
  have hp := Summable.of_nonneg_of_le
    (fun p : originalLongThinDomain (K:=K) P H => archimedeanProductDecay_nonneg _ _)
    (fun p => originalLongThinProductDecay_le_radial θ P H hP hH p) hsm
  refine ⟨hp, (hp.tsum_le_tsum (fun p => originalLongThinProductDecay_le_radial θ P H hP hH p) hsm).trans ?_⟩
  rw [tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans _ hb
  exact Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
    (fun p hp => by
      have h := originalLongThinRadius_nonneg θ P H hP.le hH.le p
      unfold originalLongThinRadialDecay
      positivity)
    (fun _ => le_rfl) hsub hs

end WaringSiegel.WSL3Poisson
