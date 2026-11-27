import WaringSiegel.WSL2TraceMajorArcUnion
import WaringSiegel.WSL2PairCount

/-!
# WSL2: uniform shifted close-pair kernel outside product major arcs

For H ≥ R², R ≥ 1, and anisotropic widths Z_v=z_v/H with z_v≥1,
the actual number of pairs is bounded by C_K product z_v^{d_v}, uniformly
in the shift η and in every aspect ratio. This is the geometric counting
step of the shifted-kernel lemma; it does not assume Poisson summation.
-/

noncomputable section
set_option maxHeartbeats 1200000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem closePairRadius_mul_arc_factor_le
    (θ : mixedSpace K) (γ : K) (R H : ℝ) (hR : 0 < R) (hH : 0 < H)
    (z : InfinitePlace K → ℝ) (hz : ∀ w, 1 ≤ z w) (w : InfinitePlace K) :
    closePairRadius θ γ R (fun v => z v / H) w *
      max 1 (R * H * normAtPlace w (θ - mixedEmbedding K γ)) ≤ 2 * R * z w := by
  let b := normAtPlace w (θ - mixedEmbedding K γ)
  have hb : 0 ≤ b := normAtPlace_nonneg _ _
  unfold closePairRadius
  change (if b = 0 then 2*R else min (2*R) (2*(z w/H)/b)) * max 1 (R*H*b) ≤ _
  by_cases hb0 : b = 0
  · rw [if_pos hb0, hb0, mul_zero, max_eq_left zero_le_one, mul_one]
    exact le_mul_of_one_le_right (by positivity) (hz w)
  · rw [if_neg hb0]
    have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    by_cases hx : R*H*b ≤ 1
    · rw [max_eq_left hx, mul_one]
      exact (min_le_left _ _).trans (le_mul_of_one_le_right (by positivity) (hz w))
    · rw [max_eq_right (le_of_not_ge hx)]
      calc
        _ ≤ (2*(z w/H)/b) * (R*H*b) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = 2*R*z w := by field_simp

theorem closePairRadius_product_arc_bound
    (θ : mixedSpace K) (γ : K) (R H : ℝ) (hR : 0 < R) (hH : 0 < H)
    (z : InfinitePlace K → ℝ) (hz : ∀ w, 1 ≤ z w) :
    (∏ w, closePairRadius θ γ R (fun v => z v/H) w ^ mult w) *
      productArcWeight (R*H) (θ-mixedEmbedding K γ) ≤
      (2*R)^finrank ℚ K * ∏ w, z w^mult w := by
  calc
    _ = ∏ w, (closePairRadius θ γ R (fun v => z v/H) w *
        max 1 (R*H*normAtPlace w (θ-mixedEmbedding K γ)))^mult w := by
      simp only [mul_pow, Finset.prod_mul_distrib, productArcWeight]
    _ ≤ ∏ w, (2*R*z w)^mult w := by
      apply Finset.prod_le_prod
      · intro w hw
        apply pow_nonneg
        exact mul_nonneg (closePairRadius_pos θ γ R hR _
          (fun v => div_pos (lt_of_lt_of_le zero_lt_one (hz v)) hH) w).le
          (le_trans zero_le_one (le_max_left _ _))
      · intro w hw
        apply pow_le_pow_left₀
        · exact mul_nonneg (closePairRadius_pos θ γ R hR _
            (fun v => div_pos (lt_of_lt_of_le zero_lt_one (hz v)) hH) w).le
            (le_trans zero_le_one (le_max_left _ _))
        · exact closePairRadius_mul_arc_factor_le θ γ R H hR hH z hz w
    _ = _ := by simp only [mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

theorem scaled_width_product (H : ℝ) (z : InfinitePlace K → ℝ) :
    (∏ w, (z w/H)^mult w) = (∏ w, z w^mult w) / H^finrank ℚ K := by
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum,
    InfinitePlace.sum_mult_eq]

/-- The small-volume case, with an exact minor-arc condition. -/
theorem closePairs_minor_small_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R H : ℝ) (hR : 1 ≤ R) (hH : 0 < H)
    (z : InfinitePlace K → ℝ) (hz : ∀ w, 1 ≤ z w)
    (hsmall : (8*R)^finrank ℚ K * (∏ w, (z w/H)^mult w) <
      (FractionalIdeal.absNorm I : ℝ))
    (hminor : ∀ γ : K, R^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
        productArcWeight (R*H) (θ-mixedEmbedding K γ)) :
    ((closePairs I θ η R (fun w => z w/H)).ncard : ℝ) ≤
      (3 : ℝ)^finrank ℚ K * (1+(2 : ℝ)^finrank ℚ K) * ∏ w, z w^mult w := by
  let B : ℝ := ∏ w, z w^mult w
  have hB : 1 ≤ B := by
    calc
      (1 : ℝ) = ∏ _w : InfinitePlace K, (1 : ℝ) := by simp
      _ ≤ B := Finset.prod_le_prod (fun _ _ => by norm_num)
        (fun w _ => one_le_pow₀ (hz w))
  have hRp : 0 < R := by linarith
  have hZ : ∀ w, 0 < z w/H := fun w => div_pos (by linarith [hz w]) hH
  by_cases hn : (closePairs I θ η R (fun w => z w/H)).Nonempty
  · obtain ⟨r, hr⟩ := hn
    obtain ⟨γ, _, _, hcount⟩ :=
      closePairs_finite_and_count I hI θ η R hR _ hZ hsmall r hr
    let Q : ℝ := Ideal.absNorm (conductorIdeal I γ)
    let A := productArcWeight (R*H) (θ-mixedEmbedding K γ)
    let V : ℝ := ∏ w, closePairRadius θ γ R (fun v => z v/H) w ^ mult w
    have hQ : 0 < Q := by
      dsimp [Q]
      exact_mod_cast conductorIdeal_absNorm_pos I hI γ
    have hA : 0 < A := productArcWeight_pos _ _
    have hV : 0 ≤ V := Finset.prod_nonneg (fun w _ =>
      pow_nonneg (closePairRadius_pos θ γ R hRp _ hZ w).le _)
    have hVA : V*A ≤ (2*R)^finrank ℚ K * B :=
      closePairRadius_product_arc_bound θ γ R H hRp hH z hz
    have hQA : R^finrank ℚ K ≤ Q*A := (hminor γ).le
    have hquot : V/Q ≤ (2 : ℝ)^finrank ℚ K * B := by
      apply (div_le_iff₀ hQ).mpr
      apply (mul_le_mul_right hA).mp
      calc
        _ ≤ (2*R)^finrank ℚ K * B := hVA
        _ = ((2 : ℝ)^finrank ℚ K * B) * R^finrank ℚ K := by rw [mul_pow]; ring
        _ ≤ ((2 : ℝ)^finrank ℚ K * B) * (Q*A) :=
          mul_le_mul_of_nonneg_left hQA (by positivity)
        _ = _ := by ring
    calc
      _ ≤ (3 : ℝ)^finrank ℚ K * (1+V/Q) := hcount
      _ ≤ (3 : ℝ)^finrank ℚ K * (B+(2 : ℝ)^finrank ℚ K*B) := by gcongr
      _ = _ := by ring
  · have he : closePairs I θ η R (fun w => z w/H) = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he, Set.ncard_empty, Nat.cast_zero]
    positivity


/-- The complementary large-volume case. The condition H≥R² is exactly
what keeps the bound independent of the scale R. -/
theorem closePairs_large_width_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R H : ℝ) (hR : 1 ≤ R) (hH : R^2 ≤ H)
    (z : InfinitePlace K → ℝ) (hz : ∀ w, 1 ≤ z w)
    (hlarge : (FractionalIdeal.absNorm I : ℝ) ≤
      (8*R)^finrank ℚ K * (∏ w, (z w/H)^mult w)) :
    ((closePairs I θ η R (fun w => z w/H)).ncard : ℝ) ≤
      (2*(3 : ℝ)^finrank ℚ K*(3 : ℝ)^finrank ℚ K *
        ((8 : ℝ)^finrank ℚ K+1)/(FractionalIdeal.absNorm I : ℝ)) *
          ∏ w, z w^mult w := by
  let d := finrank ℚ K
  let B : ℝ := ∏ w, z w^mult w
  let N : ℝ := FractionalIdeal.absNorm I
  let r := R^d
  let h := H^d
  let c : ℝ := 8^d
  have hN : 0 < N := fractionalIdeal_absNorm_pos I hI
  have hRp : 0 < R := by linarith
  have hHp : 0 < H := lt_of_lt_of_le (sq_pos_of_pos hRp) hH
  have hr : 0 < r := pow_pos hRp _
  have hh : 0 < h := pow_pos hHp _
  have hB : 0 ≤ B := Finset.prod_nonneg (fun w _ => pow_nonneg (by linarith [hz w]) _)
  have hr1 : 1 ≤ r := one_le_pow₀ hR
  have hr2 : r*r ≤ h := by
    have hp := pow_le_pow_left₀ (sq_nonneg R) hH d
    simpa only [r, h, pow_two, mul_pow] using hp
  have hrh : r ≤ h := le_trans (le_mul_of_one_le_right hr.le hr1) hr2
  have hbig : N ≤ c*r*(B/h) := by
    simpa only [scaled_width_product, mul_pow, d, B, N, r, h, c] using hlarge
  have hNr : N*r ≤ c*B := by
    have h₁ : N*h ≤ c*r*B := (le_div_iff₀ hh).mp (by
      simpa only [mul_div_assoc] using hbig)
    have h₂ : N*(r*r) ≤ c*r*B :=
      (mul_le_mul_of_nonneg_left hr2 hN.le).trans h₁
    apply (mul_le_mul_right hr).mp
    nlinarith [h₂]
  have hrbound : r ≤ c*B/N := (le_div_iff₀ hN).mpr (by simpa only [mul_comm] using hNr)
  have hsecond : r*(B/h/N) ≤ B/N := by
    have hx : r*(B/h) ≤ B := by
      rw [← mul_div_assoc]
      exact (div_le_iff₀ hh).mpr (by nlinarith)
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hx hN.le
  have hcount := closePairs_trivial_ncard_bound I hI θ η R hR
    (fun w => z w/H) (fun w => div_pos (by linarith [hz w]) hHp)
  rw [scaled_width_product] at hcount
  change ((closePairs I θ η R (fun w => z w/H)).ncard : ℝ) ≤
    (2*(3 : ℝ)^d*r)*((3 : ℝ)^d*(1+B/h/N)) at hcount
  calc
    _ ≤ (2*(3 : ℝ)^d*r)*((3 : ℝ)^d*(1+B/h/N)) := hcount
    _ = (2*(3 : ℝ)^d*(3 : ℝ)^d)*(r+r*(B/h/N)) := by ring
    _ ≤ (2*(3 : ℝ)^d*(3 : ℝ)^d)*(c*B/N+B/N) := by gcongr
    _ = _ := by dsimp [d, B, N, c]; ring

def shiftedPairConstant (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ :=
  (3 : ℝ)^finrank ℚ K * (1+(2 : ℝ)^finrank ℚ K) +
    2*(3 : ℝ)^finrank ℚ K*(3 : ℝ)^finrank ℚ K *
      ((8 : ℝ)^finrank ℚ K+1)/(FractionalIdeal.absNorm I : ℝ)

theorem shiftedPairConstant_pos (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    0 < shiftedPairConstant I := by
  have hN := fractionalIdeal_absNorm_pos I hI
  unfold shiftedPairConstant
  positivity

/-- Uniform in the actual fractional ideal, the shift, and all aspect ratios.
Only the displayed constant depends on I. -/
theorem closePairs_minor_uniform_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R H : ℝ) (hR : 1 ≤ R) (hH : R^2 ≤ H)
    (z : InfinitePlace K → ℝ) (hz : ∀ w, 1 ≤ z w)
    (hminor : ∀ γ : K, R^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
        productArcWeight (R*H) (θ-mixedEmbedding K γ)) :
    ((closePairs I θ η R (fun w => z w/H)).ncard : ℝ) ≤
      shiftedPairConstant I * ∏ w, z w^mult w := by
  have hHp : 0 < H := lt_of_lt_of_le (sq_pos_of_pos (by linarith : 0 < R)) hH
  have hN := fractionalIdeal_absNorm_pos I hI
  have hB : 0 ≤ ∏ w, z w^mult w :=
    Finset.prod_nonneg (fun w _ => pow_nonneg (by linarith [hz w]) _)
  by_cases hs : (8*R)^finrank ℚ K * (∏ w, (z w/H)^mult w) <
      (FractionalIdeal.absNorm I : ℝ)
  · exact (closePairs_minor_small_bound I hI θ η R H hR hHp z hz hs hminor).trans (by
      unfold shiftedPairConstant
      have hp : 0 ≤ 2*(3 : ℝ)^finrank ℚ K*(3 : ℝ)^finrank ℚ K *
          ((8 : ℝ)^finrank ℚ K+1)/(FractionalIdeal.absNorm I : ℝ) := by positivity
      nlinarith)
  · exact (closePairs_large_width_bound I hI θ η R H hR hH z hz (le_of_not_gt hs)).trans (by
      unfold shiftedPairConstant
      have hp : 0 ≤ (3 : ℝ)^finrank ℚ K*(1+(2 : ℝ)^finrank ℚ K) := by positivity
      nlinarith)

/-- The geometric shifted-kernel estimate on the literal trace torus. -/
theorem trace_closePairs_minor_uniform_bound
    (θ η : mixedSpace K) (R H : ℝ) (hR : 1 ≤ R) (hH : R^2 ≤ H)
    (z : InfinitePlace K → ℝ) (hz : ∀ w, 1 ≤ z w)
    (hminor : (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
      traceMajorArcUnion (R*H) (R^finrank ℚ K)) :
    ((closePairs (inverseDifferent K) θ η R (fun w => z w/H)).ncard : ℝ) ≤
      shiftedPairConstant (inverseDifferent K) * ∏ w, z w^mult w := by
  apply closePairs_minor_uniform_bound _ inverseDifferent_ne_zero θ η R H hR hH z hz
  intro γ
  by_contra hn
  apply hminor
  exact Set.mem_iUnion.mpr ⟨γ, θ, le_of_not_gt hn, rfl⟩

end WaringSiegel
