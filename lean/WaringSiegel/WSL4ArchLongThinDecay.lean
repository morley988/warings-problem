import WaringSiegel.WSL4ArchLongThinCount

/-!
# WSL2: true major-arc dual decay and Gaussian bounds

The geometric major factor is retained in the actual convergent series.
The constants depend only on the field/fractional ideal; no oscillatory
estimate or Poisson identity is used as a proof premise.
-/

noncomputable section
set_option maxHeartbeats 1200000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem longThinMajorDecay_finite_sum_bound_enlarged
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ : mixedSpace K) (P H : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2) (L : ℝ) (hL : 1 ≤ L)
    (γ : K) (hmaj : θ ∈ productMajorArc I (P^2*H) (L*P^finrank ℚ K) γ)
    (S : Finset (longThinDualDomain I)) :
    (∑ p ∈ S, longThinDualDecay θ P H p) ≤ 2*((longThinDualConstant I*L^(5*finrank ℚ K))*longThinMajorFactor I θ P H γ) := by
  have hLp : 0 < L := by linarith
  have hPp : 0 < P := by linarith
  have hHp : 0 < H := by linarith
  have hPHp : 0 < P*H := mul_pos hPp hHp
  have hF := longThinMajorFactor_one_le I hI θ P H hPp.le γ
  have hC := longThinDualConstant_pos I hI
  apply WSL2.finite_annular_decay_bound S (fun p => longThinDualRadius θ P H p)
    (fun p _ => longThinDualRadius_nonneg θ P H hPp.le p)
    (5*finrank ℚ K) ((longThinDualConstant I*L^(5*finrank ℚ K))*longThinMajorFactor I θ P H γ) (by positivity)
  intro n
  let u : ℝ := (n:ℝ)+1
  let T := S.filter (fun p : longThinDualDomain I => ⌊longThinDualRadius θ P H p⌋₊=n)
  have hu : 1 ≤ u := by dsimp [u]; have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hup : 0 < u := by linarith
  have hmaps : ∀ p ∈ (T : Set (longThinDualDomain I)),
      (p:𝓞 K × K) ∈ closePairs I θ 0 (u*P) (fun _ => u/(P*H)) := by
    intro p hp
    have hf := (Finset.mem_filter.mp hp).2
    have hrad : longThinDualRadius θ P H p ≤ u := by
      have h := Nat.lt_floor_add_one (longThinDualRadius θ P H p)
      rw [hf] at h
      exact h.le
    have hy : ‖mixedEmbedding K ((p:𝓞 K × K).1:K)‖/P ≤ u := (le_max_left _ _).trans hrad
    have he : (P*H)*‖θ*mixedEmbedding K ((p:𝓞 K × K).1:K)-
        mixedEmbedding K (p:𝓞 K × K).2‖ ≤ u := (le_max_right _ _).trans hrad
    refine ⟨p.property, ?_, ?_⟩
    · intro w
      exact (normAtPlace_le_mixed_norm _ w).trans ((div_le_iff₀ hPp).mp hy)
    · intro w
      simp only [add_zero]
      apply (le_div_iff₀ hPHp).mpr
      exact (mul_le_mul_of_nonneg_right (normAtPlace_le_mixed_norm _ w) hPHp.le).trans
        (by simpa only [mul_comm] using he)
  have hcard : T.card ≤ (closePairs I θ 0 (u*P) (fun _ => u/(P*H))).ncard := by
    simpa only [Set.ncard_coe_finset] using
      Set.ncard_le_ncard_of_injOn (s := (T : Set (longThinDualDomain I)))
        (fun p => (p:𝓞 K × K)) hmaps (fun _ _ _ _ h => Subtype.ext h)
        (closePairs_finite I hI θ 0 (u*P) (one_le_mul_of_one_le_of_one_le hu hP)
          _ (fun _ => div_pos hup hPHp))
  have hbound := longThinMajor_count_bound_enlarged I hI θ P H u L hP hH hPH hu hL γ hmaj
  have h := (Nat.cast_le.mpr hcard).trans hbound
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h


/-- Uniform major-arc radial-series bound, including its actual summability. -/
theorem longThinMajorDecay_summable_bound_enlarged
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (θ : mixedSpace K)
    (P H : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2) (L : ℝ) (hL : 1 ≤ L)
    (γ : K) (hmaj : θ ∈ productMajorArc I (P^2*H) (L*P^finrank ℚ K) γ) :
    Summable (fun p : longThinDualDomain I => longThinDualDecay θ P H p) ∧
      (∑' p : longThinDualDomain I, longThinDualDecay θ P H p) ≤
        2*((longThinDualConstant I*L^(5*finrank ℚ K))*longThinMajorFactor I θ P H γ) := by
  have hLp : 0 < L := by linarith
  have hb := longThinMajorDecay_finite_sum_bound_enlarged I hI θ P H hP hH hPH L hL γ hmaj
  have hs := summable_of_sum_le (fun p : longThinDualDomain I => by
    have hr := longThinDualRadius_nonneg θ P H (by linarith : 0 ≤ P) p
    unfold longThinDualDecay
    positivity) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

/-- The full actual dual Gaussian has precisely the required major factor
1+P^d/(Qγ A(P²H,θ−γ)), before the Poisson transfer to the original lattice. -/
theorem longThinMajorGaussian_summable_bound_enlarged
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (θ : mixedSpace K)
    (P H : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2) (L : ℝ) (hL : 1 ≤ L)
    (γ : K) (hmaj : θ ∈ productMajorArc I (P^2*H) (L*P^finrank ℚ K) γ) :
    Summable (fun p : longThinDualDomain I => longThinDualGaussian θ P H p) ∧
      (∑' p : longThinDualDomain I, longThinDualGaussian θ P H p) ≤
        (2*longThinGaussianFactor K*(longThinDualConstant I*L^(5*finrank ℚ K)))*longThinMajorFactor I θ P H γ := by
  obtain ⟨hs, hb⟩ := longThinMajorDecay_summable_bound_enlarged I hI θ P H hP hH hPH L hL γ hmaj
  have hC : 0 ≤ longThinGaussianFactor K := (Real.exp_pos _).le
  have hbound := fun p : longThinDualDomain I =>
    longThinDualGaussian_le_decay θ P H (by linarith) (by linarith) p
  have hsm := hs.mul_left (longThinGaussianFactor K)
  have hsg := Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hbound hsm
  refine ⟨hsg, (hsg.tsum_le_tsum hbound hsm).trans ?_⟩
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left hb hC).trans_eq (by ring)

#print axioms longThinMajorDecay_summable_bound_enlarged
#print axioms longThinMajorGaussian_summable_bound_enlarged
end WaringSiegel.WSL4
