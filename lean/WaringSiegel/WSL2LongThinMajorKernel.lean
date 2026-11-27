import WaringSiegel.WSL2LongThinMajorCenter
import WaringSiegel.WSL2LongThinDualGaussian
import WaringSiegel.WSL2MomentLongThinLarge

/-!
# WSL2: the major-arc bound for the actual dual long-thin kernel

The small-box slope is proved to equal the specified major center. The
large-box tail is controlled independently of θ. Together they give the
major factor 1+P^d/(Q A), uniformly for the full dual radial/Gaussian series.
-/

noncomputable section
set_option maxHeartbeats 1800000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def longThinMajorFactor (I : FractionalIdeal (𝓞 K)⁰ K) (θ : mixedSpace K)
    (P H : ℝ) (γ : K) : ℝ :=
  1+P^finrank ℚ K/((Ideal.absNorm (conductorIdeal I γ):ℝ)*
    productArcWeight (P^2*H) (θ-mixedEmbedding K γ))

theorem longThinMajorFactor_one_le
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (θ : mixedSpace K)
    (P H : ℝ) (hP : 0 ≤ P) (γ : K) : 1 ≤ longThinMajorFactor I θ P H γ := by
  have hQ : (0:ℝ) < Ideal.absNorm (conductorIdeal I γ) := by
    exact_mod_cast conductorIdeal_absNorm_pos I hI γ
  have hA := productArcWeight_pos (P^2*H) (θ-mixedEmbedding K γ)
  unfold longThinMajorFactor
  exact le_add_of_nonneg_right (div_nonneg (pow_nonneg hP _) (mul_pos hQ hA).le)

theorem longThinMajor_small_count_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (θ : mixedSpace K)
    (P H u : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hu : 1 ≤ u)
    (hsmall : (8*(u*P))^finrank ℚ K *
      (∏ w : InfinitePlace K, (u/(P*H))^mult w) < (FractionalIdeal.absNorm I : ℝ))
    (γ₀ : K) (hmaj : θ ∈ productMajorArc I (P^2*H) (P^finrank ℚ K) γ₀) :
    ((closePairs I θ 0 (u*P) (fun _ => u/(P*H))).ncard : ℝ) ≤
      longThinDualConstant I*u^(5*finrank ℚ K)*longThinMajorFactor I θ P H γ₀ := by
  have hPp : 0 < P := by linarith
  have hHp : 0 < H := by linarith
  have hup : 0 < u := by linarith
  have hUP : 1 ≤ u*P := one_le_mul_of_one_le_of_one_le hu hP
  have hZ : ∀ _w : InfinitePlace K, 0 < u/(P*H) := fun _ => div_pos hup (mul_pos hPp hHp)
  have hzero : (0,0) ∈ closePairs I θ 0 (u*P) (fun _ => u/(P*H)) := by
    refine ⟨I.zero_mem, ?_, ?_⟩ <;> intro w <;> simp only [map_zero, mul_zero,
      add_zero, sub_zero] <;> positivity
  obtain ⟨γ, hline⟩ := closePairs_affine_line I θ 0 (u*P) hUP _ (fun w => (hZ w).le) hsmall
    (0,0) hzero
  have hline₀ : ∀ p ∈ closePairs I θ 0 (u*P) (fun _ => u/(P*H)), p.2 = γ₀*(p.1:K) := by
    by_cases hn : ∃ p ∈ closePairs I θ 0 (u*P) (fun _ => u/(P*H)), p.1 ≠ 0
    · obtain ⟨p, hp, hy⟩ := hn
      have hpγ : p.2 = γ*(p.1:K) := by simpa only [map_zero, sub_zero, zero_add] using hline p hp
      have he := closePair_slope_eq_major_center I hI θ P H u hP hH hu hsmall γ₀ hmaj p hp hy γ hpγ
      intro q hq
      simpa only [map_zero, sub_zero, zero_add, he] using hline q hq
    · intro p hp
      have hy : p.1 = 0 := by by_contra h; exact hn ⟨p,hp,h⟩
      simpa only [hy, map_zero, sub_zero, mul_zero, zero_add] using hline p hp
  have hf := closePairs_finite I hI θ 0 (u*P) hUP _ hZ
  have hc := closePairs_line_card_bound I hI θ 0 (u*P) (by positivity) _ hZ (0,0) hzero γ₀
    hf.toFinset (fun p hp => hf.mem_toFinset.mp hp) (by
      intro p hp
      simpa only [map_zero, sub_zero, zero_add] using hline₀ p (hf.mem_toFinset.mp hp))
  rw [← Set.ncard_eq_toFinset_card _ hf] at hc
  let d := finrank ℚ K
  let U := u^d
  let X := P^d
  let Q : ℝ := Ideal.absNorm (conductorIdeal I γ₀)
  let A := productArcWeight (P^2*H) (θ-mixedEmbedding K γ₀)
  let V : ℝ := ∏ w, closePairRadius θ γ₀ (u*P) (fun _ => u/(P*H)) w ^ mult w
  let Y := X/(Q*A)
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast conductorIdeal_absNorm_pos I hI γ₀
  have hA : 0 < A := productArcWeight_pos _ _
  have hY : 0 ≤ Y := div_nonneg (pow_pos hPp _).le (mul_pos hQ hA).le
  have hU1 : 1 ≤ U := one_le_pow₀ hu
  have hU25 : U^2 ≤ U^5 := pow_le_pow_right₀ hU1 (by omega)
  have hU15 : 1 ≤ U^5 := one_le_pow₀ hU1
  have hV : 0 ≤ V := Finset.prod_nonneg (fun w _ =>
    pow_nonneg (closePairRadius_pos θ γ₀ (u*P) (by positivity) _ hZ w).le _)
  have hbig := closePairRadius_product_arc_bound θ γ₀ (u*P) (P*H)
    (by positivity) (by positivity) (fun _ => u) (fun _ => hu)
  have hscale : P^2*H ≤ (u*P)*(P*H) := by
    calc
      _ = 1*(P^2*H) := by ring
      _ ≤ u*(P^2*H) := mul_le_mul_of_nonneg_right hu (by positivity)
      _ = _ := by ring
  have hVA : V*A ≤ (2:ℝ)^d*U^2*X := by
    have h := (mul_le_mul_of_nonneg_left
      (productArcWeight_mono_scale _ _ hscale (θ-mixedEmbedding K γ₀)) hV).trans hbig
    simpa only [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq,
      mul_pow, d, V, A, U, X, pow_two, mul_assoc, mul_comm, mul_left_comm] using h
  have hquot : V/Q ≤ (2:ℝ)^d*U^2*Y := by
    calc
      _ = (V*A)/(Q*A) := by field_simp
      _ ≤ ((2:ℝ)^d*U^2*X)/(Q*A) := div_le_div_of_nonneg_right hVA (mul_pos hQ hA).le
      _ = _ := by dsimp [Y]; ring
  have hC : (3:ℝ)^d*(1+(2:ℝ)^d) ≤ longThinDualConstant I := by
    have hN := fractionalIdeal_absNorm_pos I hI
    unfold longThinDualConstant
    exact le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ (3:ℝ)^d*(1+V/Q) := hc
    _ ≤ (3:ℝ)^d*(1+(2:ℝ)^d*U^2*Y) := by gcongr
    _ ≤ (3:ℝ)^d*(U^5+(2:ℝ)^d*U^5*Y) := by gcongr
    _ = ((3:ℝ)^d*U^5)*(1+(2:ℝ)^d*Y) := by ring
    _ ≤ ((3:ℝ)^d*U^5)*((1+(2:ℝ)^d)*(1+Y)) := by
      gcongr
      have h2 : 0 ≤ (2:ℝ)^d := by positivity
      nlinarith
    _ = ((3:ℝ)^d*(1+(2:ℝ)^d))*U^5*(1+Y) := by ring
    _ ≤ longThinDualConstant I*U^5*(1+Y) := by gcongr
    _ = _ := by
      change longThinDualConstant I*(u^d)^5*(1+Y) =
        longThinDualConstant I*u^(5*d)*(1+Y)
      rw [← pow_mul, Nat.mul_comm d 5]

theorem longThinMajor_count_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (θ : mixedSpace K)
    (P H u : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2) (hu : 1 ≤ u)
    (γ₀ : K) (hmaj : θ ∈ productMajorArc I (P^2*H) (P^finrank ℚ K) γ₀) :
    ((closePairs I θ 0 (u*P) (fun _ => u/(P*H))).ncard : ℝ) ≤
      longThinDualConstant I*u^(5*finrank ℚ K)*longThinMajorFactor I θ P H γ₀ := by
  by_cases hs : (8*(u*P))^finrank ℚ K *
      (∏ w : InfinitePlace K, (u/(P*H))^mult w) < (FractionalIdeal.absNorm I : ℝ)
  · exact longThinMajor_small_count_bound I hI θ P H u hP hH hu hs γ₀ hmaj
  · exact (longThinDual_large_volume_count_bound I hI θ P H u hP hH hPH hu
      (le_of_not_gt hs)).trans (le_mul_of_one_le_right
        (mul_nonneg (longThinDualConstant_pos I hI).le (pow_nonneg (by linarith) _))
        (longThinMajorFactor_one_le I hI θ P H (by linarith) γ₀))

end WaringSiegel
