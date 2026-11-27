import WaringSiegel.WSL3PoissonMajorFourthKappa
import WaringSiegel.WSL3CubicKappaTruncation

/-! # Exact rational-center mass for the mixed major integral -/
noncomputable section
set_option maxHeartbeats 900000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem traceRationalCenters_nonneg_weight_sum_le (N : ℕ) (w : Ideal (𝓞 K) → ℝ)
    (hw : ∀ I, 0≤w I) :
    letI := Fintype.ofFinite (traceRationalCenters K N)
    (∑ q : traceRationalCenters K N, w (traceConductor (traceCenterRepresentative q))) ≤
      ∑ I ∈ cubicConductorCutoff N, (Ideal.absNorm I.1:ℝ)*w I.1 := by
  have he (I : Ideal (𝓞 K)) : (w I^((1:ℝ)/4))^4=w I := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (hw I)]
    norm_num
  simpa only [he] using traceRationalCenters_weight_sum_le N (fun I => w I^((1:ℝ)/4))

theorem traceRationalCenters_kappa_weight_sum_le
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0≤B v)
    (N : ℕ) (t : ℝ) :
    letI := Fintype.ofFinite (traceRationalCenters K N)
    (∑ q : traceRationalCenters K N,
      ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ)^t *
        cubicKappaIdeal B (traceConductor (traceCenterRepresentative q))^4) ≤
      ∑ I ∈ cubicConductorCutoff N, (Ideal.absNorm I.1:ℝ)^(1+t)*cubicKappa B I^4 := by
  have hh := traceRationalCenters_nonneg_weight_sum_le N
    (fun I => (Ideal.absNorm I:ℝ)^t*cubicKappaIdeal B I^4) (fun I => by positivity)
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro I hI
  have hN : 0<(Ideal.absNorm I.1:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)
  rw [Real.rpow_add hN,Real.rpow_one]
  simp only [cubicKappaIdeal_coe]
  ring

theorem traceRationalCenters_kappa_negative_half_bound
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0≤B v) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ,
      letI := Fintype.ofFinite (traceRationalCenters K N)
      (∑ q : traceRationalCenters K N,
        ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ)^(-(1/2):ℝ) *
          cubicKappaIdeal B (traceConductor (traceCenterRepresentative q))^4) ≤ C := by
  let f := fun I : {I : Ideal (𝓞 K) // I≠0} => (Ideal.absNorm I.1:ℝ)^((1:ℝ)/2)*cubicKappa B I^4
  have hs : Summable f := cubicKappa_fourth_weighted_summable B hB (1/2) (by norm_num)
  have hf : ∀ I,0≤f I := fun I => by dsimp [f]; positivity
  have ht : 0≤∑' I,f I := tsum_nonneg hf
  refine ⟨(∑' I,f I)+1,by positivity,fun N => ?_⟩
  have hb := traceRationalCenters_kappa_weight_sum_le B hB N (-(1/2):ℝ)
  norm_num only [show (1:ℝ)+-(1/2)=1/2 by norm_num] at hb
  exact (hb.trans (hs.sum_le_tsum (cubicConductorCutoff N) (fun I _ => hf I))).trans (by linarith)

theorem traceRationalCenters_kappa_truncated_bound
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0≤B v)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ t : ℝ, -ε≤t → ∀ L : ℝ, 1≤L →
      letI := Fintype.ofFinite (traceRationalCenters K ⌊L⌋₊)
      (∑ q : traceRationalCenters K ⌊L⌋₊,
        ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ)^t *
          cubicKappaIdeal B (traceConductor (traceCenterRepresentative q))^4) ≤ C*L^(t+ε) := by
  obtain ⟨C,hC,hb⟩ := cubicKappa_fourth_truncation_bound B hB ε hε
  refine ⟨C,hC,fun t ht L hL => ?_⟩
  have hcut : ∀ I ∈ cubicConductorCutoff (K:=K) ⌊L⌋₊,(Ideal.absNorm I.1:ℝ)≤L := by
    intro I hI
    have hh : (Ideal.absNorm I.1:ℝ)≤(⌊L⌋₊:ℝ) := by
      exact_mod_cast (mem_cubicConductorCutoff ⌊L⌋₊ I).mp hI
    exact hh.trans (Nat.floor_le (by linarith))
  have hh := hb (1+t) (by linarith) L hL (cubicConductorCutoff ⌊L⌋₊) hcut
  rw [show 1+t-1+ε=t+ε by ring] at hh
  exact (traceRationalCenters_kappa_weight_sum_le B hB ⌊L⌋₊ t).trans hh

#print axioms traceRationalCenters_nonneg_weight_sum_le
#print axioms traceRationalCenters_kappa_negative_half_bound
#print axioms traceRationalCenters_kappa_truncated_bound
end WaringSiegel.WSL4
