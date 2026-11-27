import WaringSiegel.WSL2ShiftedPairKernel

/-!
# WSL2: the actual dual long-thin close-pair count

For scales P≥1 and H≥1 with P≤H², count pairs with |y_v|≤uP and
|θ_v y_v-a_v|≤u/(PH), for u≥1. Outside the genuine product arcs at
scale P²H and cutoff P^[K:Q], the count is bounded by C_K u^(5[K:Q]).
The polynomial exponent is deliberately generous: rapid Gaussian or Schwartz
decay absorbs it. No Gaussian Poisson identity is assumed or asserted here.
-/

noncomputable section
set_option maxHeartbeats 1600000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem productArcWeight_mono_scale (H J : ℝ) (hHJ : H ≤ J) (β : mixedSpace K) :
    productArcWeight H β ≤ productArcWeight J β := by
  apply Finset.prod_le_prod
  · intro w hw
    exact pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  · intro w hw
    apply pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _))
    exact max_le_max_left _ (mul_le_mul_of_nonneg_right hHJ (normAtPlace_nonneg _ _))

theorem closePairs_small_denominator_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ η : mixedSpace K) (R H L : ℝ) (hR : 1 ≤ R) (hH : 0 < H) (hL : 0 < L)
    (z : InfinitePlace K → ℝ) (hz : ∀ w, 1 ≤ z w)
    (hsmall : (8*R)^finrank ℚ K * (∏ w, (z w/H)^mult w) <
      (FractionalIdeal.absNorm I : ℝ))
    (hdenom : ∀ γ : K, L ≤ (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
      productArcWeight (R*H) (θ-mixedEmbedding K γ)) :
    ((closePairs I θ η R (fun w => z w/H)).ncard : ℝ) ≤
      (3 : ℝ)^finrank ℚ K *
        (1+(2*R)^finrank ℚ K*(∏ w, z w^mult w)/L) := by
  have hRp : 0 < R := by linarith
  have hZ : ∀ w, 0 < z w/H := fun w => div_pos (by linarith [hz w]) hH
  have hzprod : 0 ≤ ∏ w, z w^mult w :=
    Finset.prod_nonneg (fun w _ => pow_nonneg (by linarith [hz w]) _)
  by_cases hn : (closePairs I θ η R (fun w => z w/H)).Nonempty
  · obtain ⟨r, hr⟩ := hn
    obtain ⟨γ, _, _, hcount⟩ := closePairs_finite_and_count I hI θ η R hR _ hZ hsmall r hr
    let Q : ℝ := Ideal.absNorm (conductorIdeal I γ)
    let A := productArcWeight (R*H) (θ-mixedEmbedding K γ)
    let V : ℝ := ∏ w, closePairRadius θ γ R (fun v => z v/H) w ^ mult w
    let B : ℝ := (2*R)^finrank ℚ K*(∏ w, z w^mult w)
    have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast conductorIdeal_absNorm_pos I hI γ
    have hA : 0 < A := productArcWeight_pos _ _
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hVA : V*A ≤ B := closePairRadius_product_arc_bound θ γ R H hRp hH z hz
    have hquot : V/Q ≤ B/L := by
      calc
        _ = (V*A)/(Q*A) := by field_simp
        _ ≤ B/(Q*A) := div_le_div_of_nonneg_right hVA (mul_pos hQ hA).le
        _ ≤ B/L := div_le_div_of_nonneg_left hB hL (hdenom γ)
    exact hcount.trans (mul_le_mul_of_nonneg_left (add_le_add_left hquot 1) (by positivity))
  · rw [Set.not_nonempty_iff_eq_empty.mp hn, Set.ncard_empty, Nat.cast_zero]
    positivity

def longThinDualConstant (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ :=
  (3 : ℝ)^finrank ℚ K*(1+(2 : ℝ)^finrank ℚ K) +
    2*(3 : ℝ)^finrank ℚ K*(3 : ℝ)^finrank ℚ K *
      (((8 : ℝ)^finrank ℚ K/(FractionalIdeal.absNorm I : ℝ))^2 +
        1/(FractionalIdeal.absNorm I : ℝ))

theorem longThinDualConstant_pos (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    0 < longThinDualConstant I := by
  have hn := fractionalIdeal_absNorm_pos I hI
  unfold longThinDualConstant
  positivity

/-- Uniform count at every enlarged dual scale. -/
theorem longThinDual_count_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ : mixedSpace K) (P H u : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (hu : 1 ≤ u)
    (hminor : ∀ γ : K, P^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
        productArcWeight (P^2*H) (θ-mixedEmbedding K γ)) :
    ((closePairs I θ 0 (u*P) (fun _ => u/(P*H))).ncard : ℝ) ≤
      longThinDualConstant I * u^(5*finrank ℚ K) := by
  let d := finrank ℚ K
  let U := u^d
  let X := P^d
  let T := H^d
  let N : ℝ := FractionalIdeal.absNorm I
  let C₁ : ℝ := (3:ℝ)^d*(1+(2:ℝ)^d)
  let C₂ : ℝ := 2*(3:ℝ)^d*(3:ℝ)^d * (((8:ℝ)^d/N)^2+1/N)
  have hPp : 0 < P := by linarith
  have hHp : 0 < H := by linarith
  have hup : 0 < u := by linarith
  have hN : 0 < N := fractionalIdeal_absNorm_pos I hI
  have hU : 0 < U := pow_pos hup _
  have hX : 0 < X := pow_pos hPp _
  have hT : 0 < T := pow_pos hHp _
  have hU1 : 1 ≤ U := one_le_pow₀ hu
  have hT1 : 1 ≤ T := one_le_pow₀ hH
  have hUP : 1 ≤ u*P := one_le_mul_of_one_le_of_one_le hu hP
  have hU25 : U^2 ≤ U^5 := pow_le_pow_right₀ hU1 (by omega)
  have hU15 : 1 ≤ U^5 := one_le_pow₀ hU1
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hpow : u^(5*d) = U^5 := by dsimp [U]; rw [← pow_mul]; congr 1; omega
  have hconstant : longThinDualConstant I = C₁+C₂ := rfl
  rw [show 5*finrank ℚ K = 5*d from rfl, hpow, hconstant]
  by_cases hs : (8*(u*P))^d*(∏ w : InfinitePlace K, (u/(P*H))^mult w) < N
  · have hb := closePairs_small_denominator_bound I hI θ 0 (u*P) (P*H) X hUP
      (mul_pos hPp hHp) hX (fun _ => u) (fun _ => hu) hs (by
        intro γ
        have hm : P^2*H ≤ (u*P)*(P*H) := by
          calc
            _ = 1*(P^2*H) := by ring
            _ ≤ u*(P^2*H) := mul_le_mul_of_nonneg_right hu (by positivity)
            _ = _ := by ring
        exact (hminor γ).le.trans (mul_le_mul_of_nonneg_left
          (productArcWeight_mono_scale _ _ hm _) (Nat.cast_nonneg _)))
    have he : (3:ℝ)^d*(1+(2*(u*P))^d*(∏w : InfinitePlace K, u^mult w)/X) =
        (3:ℝ)^d*(1+(2:ℝ)^d*U^2) := by
      simp only [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, mul_pow]
      dsimp [X, U, d]
      field_simp <;> ring
    rw [he] at hb
    calc
      _ ≤ (3:ℝ)^d*(1+(2:ℝ)^d*U^2) := hb
      _ ≤ (3:ℝ)^d*(U^5+(2:ℝ)^d*U^5) := by gcongr
      _ = C₁*U^5 := by dsimp [C₁]; ring
      _ ≤ (C₁+C₂)*U^5 := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hC₂) (pow_nonneg hU.le 5)
  · have hprod : (∏ w : InfinitePlace K, (u/(P*H))^mult w) = (u/(P*H))^d := by
      rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
    have he₀ : (8*(u*P))^d*(∏ w : InfinitePlace K, (u/(P*H))^mult w) =
        (8:ℝ)^d*U^2/T := by
      rw [hprod]
      dsimp [U, T]
      simp only [mul_pow, div_pow]
      field_simp <;> ring
    have hlarge : N ≤ (8:ℝ)^d*U^2/T := by
      rw [← he₀]
      exact le_of_not_gt hs
    have hTb : T ≤ ((8:ℝ)^d/N)*U^2 := by
      have h := (le_div_iff₀ hT).mp hlarge
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hN).mpr (by nlinarith [h])
    have hXT : X ≤ T^2 := by
      have h := pow_le_pow_left₀ hPp.le hPH d
      simpa only [X, T, ← pow_mul, mul_comm d 2] using h
    have hXb : X ≤ ((8:ℝ)^d/N)^2*U^4 := by
      have ht := pow_le_pow_left₀ hT.le hTb 2
      calc
        X ≤ T^2 := hXT
        _ ≤ (((8:ℝ)^d/N)*U^2)^2 := ht
        _ = _ := by ring
    have hsecond : U^2/(T*N) ≤ U^2/N :=
      div_le_div_of_nonneg_left (sq_nonneg U) hN (by nlinarith)
    have hb := closePairs_trivial_ncard_bound I hI θ 0 (u*P) hUP
      (fun _ => u/(P*H)) (fun _ => div_pos hup (mul_pos hPp hHp))
    have he : (2*(3:ℝ)^d*(u*P)^d)*((3:ℝ)^d*
        (1+(∏ w : InfinitePlace K, (u/(P*H))^mult w)/N)) =
        (2*(3:ℝ)^d*(3:ℝ)^d)*(U*X+U^2/(T*N)) := by
      rw [hprod]
      dsimp [U, X, T]
      simp only [mul_pow, div_pow]
      field_simp <;> ring
    rw [he] at hb
    calc
      _ ≤ (2*(3:ℝ)^d*(3:ℝ)^d)*(U*X+U^2/(T*N)) := hb
      _ ≤ (2*(3:ℝ)^d*(3:ℝ)^d)*
          (U*(((8:ℝ)^d/N)^2*U^4)+U^2/N) := by gcongr
      _ = (2*(3:ℝ)^d*(3:ℝ)^d)*(((8:ℝ)^d/N)^2*U^5+U^2/N) := by ring
      _ ≤ (2*(3:ℝ)^d*(3:ℝ)^d)*(((8:ℝ)^d/N)^2*U^5+U^5/N) := by gcongr
      _ = C₂*U^5 := by dsimp [C₂]; ring
      _ ≤ (C₁+C₂)*U^5 := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hC₁) (pow_nonneg hU.le 5)

end WaringSiegel
