import WaringSiegel.WSL4SmoothMixedSources
import WaringSiegel.WSL4MixedSixthBound

/-! # The unconditional mixed-sixth estimate for the actual smooth auxiliary sums -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem smoothAuxiliaryMixedMoment_bound
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p),
      (p:ℝ)^7≤P →
      smoothAuxiliaryMixedMoment (K:=K) ρ R hρ hR P hP p hp ≤
        C*(P^finrank ℚ K:ℝ)^((7:ℝ)/2+ε)*
          ((p:ℝ)^finrank ℚ K:ℝ)^(-(9/2):ℝ) := by
  obtain ⟨C,hC,hbound⟩ := mixedSixthBoxIntegral_single_bound (K:=K) ε hε
  let T : ℝ := max 1 (2*R)
  have hT1 : 1≤T := le_max_left _ _
  have hT2 : 2*R≤T := le_max_right _ _
  have hT0 : 0<T := lt_of_lt_of_le zero_lt_one hT1
  refine ⟨C*(T^finrank ℚ K:ℝ)^((7:ℝ)/2+ε),by positivity,?_⟩
  intro P hP p hp hpow
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
  let X := compactIntegerSupport (smoothWeightSchwartz (K:=K) ρ R hρ hR)
    (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) P hP.ne'
  let Y := compactIntegerSupport (smoothWeightSchwartz (K:=K) ρ R hρ hR)
    (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) (P/(p:ℝ))
      (div_pos hP hp0).ne'
  have hTP : P≤T*P := le_mul_of_one_le_left hP.le hT1
  have hx : ∀x∈X,‖mixedEmbedding K (x:K)‖≤T*P := by
    intro x hx
    exact (smoothIntegerSupport_norm ρ R hρ hR P hP x hx).trans
      (by simpa only [mul_comm P T] using mul_le_mul_of_nonneg_left hT2 hP.le)
  have hy : ∀y∈Y,‖mixedEmbedding K (y:K)‖≤T*P/(p:ℝ) := by
    intro y hy
    apply (smoothIntegerSupport_norm ρ R hρ hR (P/(p:ℝ)) (div_pos hP hp0) y hy).trans
    calc
      _ ≤ (P/(p:ℝ))*T := mul_le_mul_of_nonneg_left hT2 (div_nonneg hP.le hp0.le)
      _ = _ := by ring
  have hlo : ∀v:InfinitePlace K,(p:ℝ)≤v ((p:𝓞 K):K) := by
    intro v
    simp only [map_natCast,infinitePlace_natCast,le_refl]
  have hhi : ‖mixedEmbedding K ((p:𝓞 K):K)‖≤2*(p:ℝ) := by
    have hh := mixedEmbedding_natCast_norm_le (K:=K) p
    simpa only [map_natCast] using hh.trans (by linarith)
  have hb := hbound (T*P) (p:ℝ) hp1 (hpow.trans hTP) (p:𝓞 K) X Y hx hlo hhi hy
  calc
    _ ≤ mixedSixthBoxIntegral (p:𝓞 K) X Y :=
      smoothAuxiliaryMixedMoment_le_unweighted ρ R hρ hR P hP p hp
    _ ≤ _ := hb
    _ = _ := by
      rw [mul_pow,Real.mul_rpow (pow_nonneg hT0.le _) (pow_nonneg hP.le _)]
      ring

#print axioms smoothAuxiliaryMixedMoment_bound
end WaringSiegel.WSL4Local
