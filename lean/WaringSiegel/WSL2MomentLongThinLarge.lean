import WaringSiegel.WSL2LongThinDualCount

/-!
# Unconditional large-volume long-thin dual count

This isolates the large-volume packing branch.  Its hypotheses contain no
minor-arc or rational-center exclusion; this branch therefore applies to
major-arc Gaussian dual counts as well.
-/

noncomputable section
set_option maxHeartbeats 1600000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem longThinDual_large_volume_count_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ : mixedSpace K) (P H u : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (hu : 1 ≤ u)
    (hlargeInput : (FractionalIdeal.absNorm I : ℝ) ≤
      (8*(u*P))^finrank ℚ K * (∏ w : InfinitePlace K, (u/(P*H))^mult w)) :
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
  have hprod : (∏ w : InfinitePlace K, (u/(P*H))^mult w) = (u/(P*H))^d := by
    rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  have he₀ : (8*(u*P))^d*(∏ w : InfinitePlace K, (u/(P*H))^mult w) =
      (8:ℝ)^d*U^2/T := by
    rw [hprod]
    dsimp [U, T]
    simp only [mul_pow, div_pow]
    field_simp <;> ring
  have hlarge : N ≤ (8:ℝ)^d*U^2/T := by
    rw [← he₀]
    exact hlargeInput
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
