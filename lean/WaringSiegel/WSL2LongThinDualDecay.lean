import WaringSiegel.WSL2LongThinDualCount
import WaringSiegel.WSL2ConductorScaling
import WaringSiegel.WSL2MomentLatticeDecay

/-!
# WSL2: convergent dual long-thin decay kernels outside the actual major arcs

The summation runs over every algebraic integer and every member of the
fractional ideal. Both the y-variable and the approximation error decay.
The resulting sum is bounded uniformly at scales P≤H². This is the dual
geometric estimate in the long-thin argument, before Gaussian Poisson.
-/

noncomputable section
set_option maxHeartbeats 1200000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def longThinDualDomain (I : FractionalIdeal (𝓞 K)⁰ K) : Set (𝓞 K × K) := {p | p.2 ∈ I}

def longThinDualRadius (θ : mixedSpace K) (P H : ℝ) (p : 𝓞 K × K) : ℝ :=
  max (‖mixedEmbedding K (p.1:K)‖/P)
    ((P*H)*‖θ*mixedEmbedding K (p.1:K)-mixedEmbedding K p.2‖)

def longThinDualDecay (θ : mixedSpace K) (P H : ℝ) (p : 𝓞 K × K) : ℝ :=
  1/(1+longThinDualRadius θ P H p)^(5*finrank ℚ K+2)

theorem longThinDualRadius_nonneg (θ : mixedSpace K) (P H : ℝ)
    (hP : 0 ≤ P) (p : 𝓞 K × K) : 0 ≤ longThinDualRadius θ P H p :=
  le_trans (div_nonneg (norm_nonneg _) hP) (le_max_left _ _)

theorem longThinDualDecay_finite_sum_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ : mixedSpace K) (P H : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (hminor : ∀ γ : K, P^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
        productArcWeight (P^2*H) (θ-mixedEmbedding K γ))
    (S : Finset (longThinDualDomain I)) :
    (∑ p ∈ S, longThinDualDecay θ P H p) ≤ 2*longThinDualConstant I := by
  have hPp : 0 < P := by linarith
  have hHp : 0 < H := by linarith
  have hPHp : 0 < P*H := mul_pos hPp hHp
  apply WSL2.finite_annular_decay_bound S (fun p => longThinDualRadius θ P H p)
    (fun p _ => longThinDualRadius_nonneg θ P H hPp.le p)
    (5*finrank ℚ K) (longThinDualConstant I) (longThinDualConstant_pos I hI).le
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
  have hbound := longThinDual_count_bound I hI θ P H u hP hH hPH hu hminor
  exact (Nat.cast_le.mpr hcard).trans hbound

/-- The actual full dual radial series, with its uniform bound. -/
theorem longThinDualDecay_summable_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ : mixedSpace K) (P H : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (hminor : ∀ γ : K, P^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
        productArcWeight (P^2*H) (θ-mixedEmbedding K γ)) :
    Summable (fun p : longThinDualDomain I => longThinDualDecay θ P H p) ∧
      (∑' p : longThinDualDomain I, longThinDualDecay θ P H p) ≤ 2*longThinDualConstant I := by
  have hb := longThinDualDecay_finite_sum_bound I hI θ P H hP hH hPH hminor
  have hs := summable_of_sum_le (fun p : longThinDualDomain I => by
    have hr := longThinDualRadius_nonneg θ P H (by linarith : 0 ≤ P) p
    unfold longThinDualDecay
    positivity) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

theorem trace_longThinDualDecay_summable_bound
    (θ : mixedSpace K) (P H : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (k : ℕ) (hk : 0 < k)
    (hminor : (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
      traceMajorArcUnion (P^2*H) ((k:ℝ)^finrank ℚ K * P^finrank ℚ K)) :
    Summable (fun p : longThinDualDomain (inverseDifferent K) =>
      longThinDualDecay ((k:ℝ) • θ) P H p) ∧
      (∑' p : longThinDualDomain (inverseDifferent K),
        longThinDualDecay ((k:ℝ) • θ) P H p) ≤ 2*longThinDualConstant (inverseDifferent K) := by
  apply longThinDualDecay_summable_bound _ inverseDifferent_ne_zero ((k:ℝ) • θ) P H hP hH hPH
  exact traceMajorArcUnion_smul_nat_preimage (P^2*H) (P^finrank ℚ K)
    (by positivity) θ k hk hminor

end WaringSiegel
