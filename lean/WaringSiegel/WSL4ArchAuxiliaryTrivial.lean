import WaringSiegel.WSL4ArchAuxiliaryApproximation
import WaringSiegel.WSL3MomentCompactTrivial

/-! # Uniform size and continuity of the actual auxiliary cubic sources -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators SchwartzMap nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem compactCoprimeTraceCubicSum_continuous
    (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P≠0) (p : ℕ) (r : ArchimedeanTraceTorus K) :
    Continuous (fun q => compactCoprimeTraceCubicSum w P p q r) := by
  simp_rw [compactCoprimeTraceCubicSum_eq_finite w hc P hP p,finiteLinearTraceSum]
  apply continuous_finset_sum
  intro x hx
  exact (continuous_const.mul (traceTorusCharacter_continuous (x^3))).mul continuous_const

theorem compactCoprimeTraceCubicSum_trivial_bound
    (f : 𝓢(mixedSpace K,ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ)) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ), 1≤P → ∀ (p : ℕ) (q r : ArchimedeanTraceTorus K),
      ‖compactCoprimeTraceCubicSum f P p q r‖ ≤ C*P^finrank ℚ K := by
  obtain ⟨A,hA,hsupport⟩ := compact_support_place_bound (f : mixedSpace K → ℂ) hc
  let W : ℝ := 1+SchwartzMap.seminorm ℝ 0 0 f
  have hW : 0<W := by dsimp [W]; positivity
  refine ⟨2*(3:ℝ)^finrank ℚ K*A^finrank ℚ K*W,by positivity,fun P hP p q r => ?_⟩
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  let S := (compactIntegerSupport f hc P hP0.ne').filter (fun x =>
    IsUnit (Ideal.Quotient.mk (Ideal.span ({(p:𝓞 K)} : Set (𝓞 K))) x))
  have hS : ∀ x∈S, ∀ v : InfinitePlace K, v (x:K)≤A*P := by
    intro x hx v
    exact hsupport P hP0 x ((mem_compactIntegerSupport _ _ _ _ _).mp (Finset.mem_filter.mp hx).1) v
  have hcard := integer_box_card_bound S (A*P) (one_le_mul_of_one_le_of_one_le hA hP) hS
  have hw (x : 𝓞 K) : ‖f (P⁻¹ • mixedEmbedding K (x:K))‖≤W :=
    (SchwartzMap.norm_le_seminorm ℝ f _).trans (by dsimp [W]; linarith)
  rw [compactCoprimeTraceCubicSum_eq_finite f hc P hP0.ne']
  change ‖∑ x∈S,f (P⁻¹ • mixedEmbedding K (x:K))*traceTorusCharacter (x^3) q*traceTorusCharacter x r‖≤_
  calc
    _ ≤ ∑ x∈S,‖f (P⁻¹ • mixedEmbedding K (x:K))‖ := by
      apply (norm_sum_le _ _).trans_eq
      simp only [norm_mul,traceTorusCharacter,norm_latticeCharacter_eq_one,mul_one]
    _ ≤ (S.card:ℝ)*W := by
      simpa only [Finset.sum_const,nsmul_eq_mul] using
        Finset.sum_le_sum (s:=S) (fun x _ => hw x)
    _ ≤ (2*(3:ℝ)^finrank ℚ K*(A*P)^finrank ℚ K)*W :=
      mul_le_mul_of_nonneg_right hcard hW.le
    _ = _ := by rw [mul_pow]; ring

theorem auxiliary_root_sources_trivial_bound (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (p : ℕ) (hp : 0<p) (hsmall : 1≤P/(p:ℝ)),
      ∀ q : ArchimedeanTraceTorus K,
      ‖compactCoprimeTraceCubicSum (smoothWeightSchwartz rho R hrho hR) P p q 0‖≤C*P^finrank ℚ K ∧
      ‖smoothTraceSource 3 rho R hrho hR (P/(p:ℝ)) (by linarith)
        (traceTorusMul ((p:𝓞 K)^3) q)‖≤C*(P/(p:ℝ))^finrank ℚ K := by
  obtain ⟨CF,hCF,hf⟩ := compactCoprimeTraceCubicSum_trivial_bound
    (smoothWeightSchwartz (K:=K) rho R hrho hR) (smoothWeightSchwartz_hasCompactSupport rho R hrho hR)
  obtain ⟨CG,hCG,hg⟩ := compactTraceWeylSum_trivial_bound
    (smoothWeightSchwartz (K:=K) rho R hrho hR) (smoothWeightSchwartz_hasCompactSupport rho R hrho hR)
  refine ⟨CF+CG,add_pos hCF hCG,fun P p hp hsmall q => ?_⟩
  have hpR : 1≤(p:ℝ) := by exact_mod_cast hp
  have hp0 : 0<(p:ℝ) := lt_of_lt_of_le zero_lt_one hpR
  have hpP : (p:ℝ)≤P := by simpa only [one_mul] using (le_div_iff₀ hp0).mp hsmall
  have hP : 1≤P := hpR.trans hpP
  constructor
  · exact (hf P hP p q 0).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCG.le)
      (pow_nonneg (lt_of_lt_of_le zero_lt_one hP).le _))
  · exact (hg (P/(p:ℝ)) hsmall 3 (traceTorusMul ((p:𝓞 K)^3) q)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCF.le)
        (pow_nonneg (lt_of_lt_of_le zero_lt_one hsmall).le _))

#print axioms compactCoprimeTraceCubicSum_continuous
#print axioms compactCoprimeTraceCubicSum_trivial_bound
#print axioms auxiliary_root_sources_trivial_bound
end WaringSiegel.WSL4
