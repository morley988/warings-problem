import WaringSiegel.WSL4KappaLocalShift

/-! # Finite exceptional-prime comparison of actual ideal kappa weights -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem cubicKappa_eq_prod_support
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K)→ℝ)
    (I : {I:Ideal (𝓞 K)//I≠0}) :
    cubicKappa B I=∏ v∈idealPrimeSupport I.1 I.2,
      cubicKappaAt (Ideal.absNorm v.asIdeal) (B v) (cubicKappaGood v) (idealPrimeExponent I.1 v) := by
  unfold cubicKappa nonzeroIdealConductorGraph
  rw [Finset.prod_image (fun _ _ _ _ h => congrArg Prod.fst h)]
  apply Finset.prod_congr rfl
  intro v hv
  simp only [cubicKappaAt,ne_of_gt (idealPrimeExponent_pos_of_mem I.1 I.2 v hv),if_false]

theorem cubicKappa_eq_prod_superset
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K)→ℝ)
    (I : {I:Ideal (𝓞 K)//I≠0})
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : idealPrimeSupport I.1 I.2⊆S) :
    cubicKappa B I=∏ v∈S,
      cubicKappaAt (Ideal.absNorm v.asIdeal) (B v) (cubicKappaGood v) (idealPrimeExponent I.1 v) := by
  rw [cubicKappa_eq_prod_support]
  apply Finset.prod_subset hS
  intro v hv hvI
  rw [idealPrimeExponent_eq_zero_of_not_mem_support I.1 I.2 v hvI,cubicKappaAt_zero]

def kappaLossConstant
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K)→ℝ)
    (A : {I:Ideal (𝓞 K)//I≠0}) : ℝ :=
  ∏ v∈idealPrimeSupport A.1 A.2,
    max 1 (B v)⁻¹*(Ideal.absNorm v.asIdeal:ℝ)^((idealPrimeExponent A.1 v:ℝ)/3)

theorem kappaLossConstant_pos
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K)→ℝ)
    (A : {I:Ideal (𝓞 K)//I≠0}) : 0<kappaLossConstant B A := by
  apply Finset.prod_pos
  intro v hv
  apply mul_pos
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · exact Real.rpow_pos_of_pos (by linarith [cubicKappa_residue_norm_ge_two v]) _

theorem cubicKappa_bounded_conductor_loss
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K)→ℝ) (hB : ∀ v,0<B v)
    (A I J : {I:Ideal (𝓞 K)//I≠0})
    (hA : ∀ v∈idealPrimeSupport A.1 A.2,cubicKappaGood v=false)
    (hJI : ∀ v,idealPrimeExponent J.1 v ≤ idealPrimeExponent I.1 v)
    (hIJ : ∀ v,idealPrimeExponent I.1 v ≤ idealPrimeExponent J.1 v+idealPrimeExponent A.1 v) :
    cubicKappa B J≤kappaLossConstant B A*cubicKappa B I := by
  let S := (idealPrimeSupport I.1 I.2∪idealPrimeSupport J.1 J.2)∪idealPrimeSupport A.1 A.2
  have hIS : idealPrimeSupport I.1 I.2⊆S := by intro v hv; exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hJS : idealPrimeSupport J.1 J.2⊆S := by intro v hv; exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hAS : idealPrimeSupport A.1 A.2⊆S := by intro v hv; exact Finset.mem_union_right _ hv
  let D := fun v:IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
    if v∈idealPrimeSupport A.1 A.2 then
      max 1 (B v)⁻¹*(Ideal.absNorm v.asIdeal:ℝ)^((idealPrimeExponent A.1 v:ℝ)/3) else 1
  have hD : (∏ v∈S,D v)=kappaLossConstant B A := by
    rw [← Finset.prod_subset hAS (by intro v hv hvA; simp only [D,hvA,if_false])]
    apply Finset.prod_congr rfl
    intro v hv
    simp only [D,hv,if_true]
  rw [cubicKappa_eq_prod_superset B J S hJS,cubicKappa_eq_prod_superset B I S hIS,← hD,← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro v hv
    exact cubicKappaAt_nonneg _ _ _ _ (by positivity) (hB v).le
  · intro v hv
    by_cases hvA : v∈idealPrimeSupport A.1 A.2
    · simp only [D,hvA,if_true,hA v hvA]
      exact cubicKappaAt_bad_bounded_loss _ _ (by linarith [cubicKappa_residue_norm_ge_two v])
        (hB v) _ _ _ (hJI v) (hIJ v)
    · have he : idealPrimeExponent I.1 v=idealPrimeExponent J.1 v := by
        have h := hIJ v
        rw [idealPrimeExponent_eq_zero_of_not_mem_support A.1 A.2 v hvA,Nat.add_zero] at h
        exact le_antisymm h (hJI v)
      simp only [D,hvA,if_false,he,one_mul,le_refl]

theorem cubicKappa_four_mul_bound
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K)→ℝ) (hB : ∀ v,0<B v) :
    ∃ C:ℝ,0<C ∧ ∀ γ:K,
      cubicKappa B ⟨traceConductor (4*γ),traceConductor_ne_zero (4*γ)⟩≤
        C*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩ := by
  let A : {I:Ideal (𝓞 K)//I≠0} := ⟨Ideal.span ({(4:𝓞 K)}:Set (𝓞 K)),
    mt Ideal.span_singleton_eq_bot.mp (by norm_num)⟩
  refine ⟨kappaLossConstant B A,kappaLossConstant_pos B A,fun γ => ?_⟩
  apply cubicKappa_bounded_conductor_loss B hB A
  · exact cubicKappaGood_eq_false_of_four_support
  · intro v
    simpa only [map_ofNat,NumberField.RingOfIntegers.coe_eq_algebraMap] using
      (traceConductor_integral_mul_exponent_bounds (4:𝓞 K) (by norm_num) γ v).1
  · intro v
    simpa only [map_ofNat,NumberField.RingOfIntegers.coe_eq_algebraMap] using
      (traceConductor_integral_mul_exponent_bounds (4:𝓞 K) (by norm_num) γ v).2

#print axioms cubicKappa_bounded_conductor_loss
#print axioms cubicKappa_four_mul_bound
end WaringSiegel.WSL4Local
