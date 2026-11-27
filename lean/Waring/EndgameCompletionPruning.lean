import Waring.EndgameCompletionPruningSets

/-! # Actual ordinary pruning from the proved model tails -/

noncomputable section
open MeasureTheory Filter Asymptotics
open scoped BigOperators ENNReal Topology

namespace Waring.EndgameCompletion
open MixedEndgame RestrictedSmoothArcs

theorem intervalIntegrable_comp_add_of_local {F : ℝ→ℝ}
    (hF : ∀ a b : ℝ,IntegrableOn F (Set.Icc a b)) {a b : ℝ} (hab : a≤b) (c : ℝ) :
    IntervalIntegrable (fun x=>F (c+x)) volume a b := by
  have hi : IntervalIntegrable F volume (c+a) (c+b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (add_le_add_left hab c)).mpr (hF _ _)
  convert hi.comp_add_left c using 1 <;> ring

theorem ordinary_pruned_rational_arc_le (k s N : ℕ) (hk : 2≤k) (hks : k<s)
    {C : ℝ} (hC : 0<C)
    (happrox : ∀ (q : ℕ) [NeZero q] (a : ℕ) (P β : ℝ),
      Nat.Coprime a q → 0≤P → |β| *(k : ℝ)*P^(k-1)≤1/(2*(q : ℝ)) →
      ‖ordinaryWeyl k P ((a : ℝ)/q+β)-
        (completeMonomialSumMod q k (a : ZMod q)/(q : ℂ))*monomialIntegral k P β‖ ≤
        C*(q : ℝ)^(49/64 : ℝ))
    {P : ℝ} (hP : 1≤P) (q : ℕ) [NeZero q] (hqP : (q : ℝ)≤P) :
    rationalArcSum q (prunedOrdinaryFunction k s P N) (broadArcWidth k P) ≤
      (2 : ℝ)^(s-1)*(ordinaryMajorModelMoment q k s P (scaledTailSet q k P N)+
        rationalArcSum q (fun _=>(C*P^(49/64 : ℝ))^s) (broadArcWidth k P)) := by
  classical
  have hPpos : 0<P := zero_lt_one.trans_le hP
  have hδ : 0≤broadArcWidth k P := (broadArcWidth_pos (by omega) hPpos).le
  have hend : -(broadArcWidth k P/(q : ℝ))≤broadArcWidth k P/(q : ℝ) := by
    have := div_nonneg hδ (Nat.cast_nonneg q)
    linarith
  let E : ℝ := C*P^(49/64 : ℝ)
  have hE : 0≤E := by dsimp [E]; positivity
  let T := scaledTailSet q k P N
  have hT : MeasurableSet T := scaledTailSet_measurable q k P N
  have ht0 (a : (ZMod q)ˣ) (β : ℝ) :
      0≤T.indicator (fun x=>‖ordinaryMajorModel q k P a x‖^s) β :=
    Set.indicator_nonneg (fun x _=>pow_nonneg (norm_nonneg _) s) _
  have hpoint (a : (ZMod q)ˣ) {β : ℝ}
      (hβ : β∈Set.Icc (-(broadArcWidth k P/(q : ℝ))) (broadArcWidth k P/(q : ℝ))) :
      prunedOrdinaryFunction k s P N (((a : ZMod q).val : ℝ)/q+β) ≤
        (2 : ℝ)^(s-1)*(T.indicator (fun x=>‖ordinaryMajorModel q k P a x‖^s) β+E^s) := by
    by_cases hcore : (((a : ZMod q).val : ℝ)/q+β)∈rectangleCoreGlobal k P N
    · rw [prunedOrdinaryFunction,Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hcore)]
      exact mul_nonneg (by positivity) (add_nonneg (ht0 a β) (pow_nonneg hE s))
    · rw [prunedOrdinaryFunction,Set.indicator_of_mem hcore,
        Set.indicator_of_mem (outside_rectangle_mem_scaledTail k N hPpos q a hcore)]
      apply norm_pow_le_of_sub_le s hE
      have hh := happrox q (a : ZMod q).val P β (ZMod.val_coe_unit_coprime a) hPpos.le
        (broad_band_derivative (by omega) hPpos q hβ)
      simp only [ZMod.natCast_zmod_val] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg q) hqP (by norm_num)) hC.le)
  have hint (a : (ZMod q)ˣ) :
      (∫ β in -(broadArcWidth k P/(q : ℝ))..broadArcWidth k P/(q : ℝ),
        prunedOrdinaryFunction k s P N (((a : ZMod q).val : ℝ)/q+β)) ≤
      (2 : ℝ)^(s-1)*((∫ β in T, ‖ordinaryMajorModel q k P a β‖^s)+
        ∫ β in -(broadArcWidth k P/(q : ℝ))..broadArcWidth k P/(q : ℝ), E^s) := by
    have hf := intervalIntegrable_comp_add_of_local (prunedOrdinaryFunction_integrableOn k s P N)
      hend (((a : ZMod q).val : ℝ)/q)
    have hm := (ordinaryMajorModel_integrable q k s (by omega) hks hPpos.le a).indicator hT
    have hb := intervalIntegral.integral_mono_on (μ := volume) hend hf
      ((hm.intervalIntegrable.add intervalIntegrable_const).const_mul ((2 : ℝ)^(s-1)))
      (fun β hβ=>hpoint a hβ)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hm.intervalIntegrable intervalIntegrable_const] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add_right
    rw [intervalIntegral.integral_of_le hend,← integral_indicator hT]
    exact setIntegral_le_integral hm (Filter.Eventually.of_forall (ht0 a))
  unfold rationalArcSum ordinaryMajorModelMoment
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _=>hint a)

theorem sum_scaled_tail_model_le (S : Finset ℕ+) (k s N : ℕ)
    (hk : 1≤k) (hks : k<s) {P : ℝ} (hP : 0<P)
    (hsum : Summable (completeCoefficient k s)) :
    (∑ q∈S,ordinaryMajorModelMoment (q : ℕ) k s P (scaledTailSet (q : ℕ) k P N)) ≤
      P^(s-k)*normalizedPruningModelMass k s N := by
  let f : ℕ→ℝ := fun q=>completeCoefficient k s q*
    ∫ β in {β : ℝ | N≤q ∨ (N : ℝ)< |β|},‖monomialIntegral k 1 β‖^s
  have hf0 (q : ℕ) : 0≤f q := mul_nonneg (completeCoefficient_nonneg k s q)
    (integral_nonneg (fun β=>pow_nonneg (norm_nonneg _) s))
  have hmajor := hsum.mul_right (∫ β : ℝ,‖monomialIntegral k 1 β‖^s)
  have hf : Summable f := Summable.of_nonneg_of_le hf0 (fun q=>
    mul_le_mul_of_nonneg_left (setIntegral_le_integral
      (integrable_monomial_moment k s hk hks (P := 1) zero_le_one)
      (Filter.Eventually.of_forall (fun β=>pow_nonneg (norm_nonneg _) s)))
      (completeCoefficient_nonneg k s q)) hmajor
  have hsumle := hf.sum_le_tsum (S.image (fun q : ℕ+ => (q : ℕ))) (fun q _=>hf0 q)
  rw [Finset.sum_image (g := fun q : ℕ+ => (q : ℕ)) (f := f)
    (fun (q : ℕ+) _ (r : ℕ+) _ h=>Subtype.ext h)] at hsumle
  have he (q : ℕ+) : ordinaryMajorModelMoment (q : ℕ) k s P (scaledTailSet (q : ℕ) k P N)=
      P^(s-k)*f (q : ℕ) := by
    rw [ordinaryMajorModelMoment_factorization,scaled_monomial_tail_integral (q : ℕ) k s N hks.le hP]
    dsimp [f]
    rw [completeCoefficient_nezero]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hsumle (pow_nonneg hP.le _)

theorem ordinary_pruned_arc_sum_bound (k s : ℕ) (hk : 2≤k) (hs : 11≤s)
    (hks : k<s) (hsum : Summable (completeCoefficient k s)) :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P → ∀ N : ℕ,∀ S : Finset ℕ+,
      (∀ q∈S,(q : ℝ)≤P) →
      (∑ q∈S,rationalArcSum (q : ℕ) (prunedOrdinaryFunction k s P N) (broadArcWidth k P)) ≤
        (2 : ℝ)^(s-1)*(P^(s-k)*normalizedPruningModelMass k s N+C^s*P^((s : ℝ)-k-1/2)) := by
  obtain ⟨C,hC,happrox⟩ := ordinary_broad_major_approximation k hk (ε := (1/64 : ℝ)) (by norm_num)
  norm_num only [show (3/4 : ℝ)+1/64=49/64 by norm_num] at happrox
  refine ⟨C,hC,?_⟩
  intro P hP N S hSP
  have hPpos := zero_lt_one.trans_le hP
  have hδ := (broadArcWidth_pos (by omega : 1≤k) hPpos).le
  have hmodels := sum_scaled_tail_model_le S k s N (by omega) hks hPpos hsum
  have herr : (∑ q∈S,rationalArcSum (q : ℕ) (fun _=>(C*P^(49/64 : ℝ))^s) (broadArcWidth k P)) ≤
      C^s*P^((s : ℝ)-k-1/2) := by
    exact (sum_constant_arc_integrals_le S hPpos.le hSP hδ (by positivity)).trans
      (broad_error_mass_le k s (by omega) hs hP hC.le)
  calc
    _ ≤ ∑ q∈S,(2 : ℝ)^(s-1)*(ordinaryMajorModelMoment (q : ℕ) k s P (scaledTailSet (q : ℕ) k P N)+
        rationalArcSum (q : ℕ) (fun _=>(C*P^(49/64 : ℝ))^s) (broadArcWidth k P)) :=
      Finset.sum_le_sum (fun q hq=>ordinary_pruned_rational_arc_le k s N hk hks hC happrox hP
        (q : ℕ) (hSP q hq))
    _ = (2 : ℝ)^(s-1)*((∑ q∈S,ordinaryMajorModelMoment (q : ℕ) k s P (scaledTailSet (q : ℕ) k P N))+
        ∑ q∈S,rationalArcSum (q : ℕ) (fun _=>(C*P^(49/64 : ℝ))^s) (broadArcWidth k P)) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hmodels herr) (by positivity)

def ordinaryPruning (k : ℕ) (P : ℝ) (N : ℕ) : Set ℝ :=
  ordinaryBroadMajor k P \ rectangleCoreGlobal k P N

def ordinaryPruningMoment (k s : ℕ) (P : ℝ) (N : ℕ) : ℝ :=
  ∫ α in ordinaryPruning k P N,‖ordinaryWeyl k P α‖^s

theorem ordinaryPruning_measurable (k : ℕ) (P : ℝ) (N : ℕ) :
    MeasurableSet (ordinaryPruning k P N) :=
  (ordinaryBroadMajor_measurable k P).diff (rectangleCoreGlobal_measurable k P N)

theorem ordinaryPruning_subset (k : ℕ) (P : ℝ) (N : ℕ) :
    ordinaryPruning k P N⊆Set.Ioc 0 1 := Set.diff_subset.trans (ordinaryBroadMajor_subset k P)

theorem ordinaryPruningMoment_nonneg (k s : ℕ) (P : ℝ) (N : ℕ) :
    0≤ordinaryPruningMoment k s P N := integral_nonneg (fun _=>pow_nonneg (norm_nonneg _) s)

theorem ordinaryArcMoment_pruning_eq (k s : ℕ) (P : ℝ) (N : ℕ) :
    ordinaryArcMoment k s P (ordinaryPruning k P N)=ENNReal.ofReal (ordinaryPruningMoment k s P N) := by
  have hi : IntegrableOn (fun α=>‖ordinaryWeyl k P α‖^s) (ordinaryPruning k P N) :=
    ((continuous_ordinary k P).norm.pow s).integrableOn_Icc.mono_set
      ((ordinaryPruning_subset k P N).trans Set.Ioc_subset_Icc_self)
  unfold ordinaryArcMoment ordinaryPruningMoment absoluteOrdinary
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun α=>pow_nonneg (norm_nonneg _) s))]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _)]

theorem integral_prunedOrdinaryFunction (k s : ℕ) (P : ℝ) (N : ℕ) :
    (∫ α in ordinaryBroadMajor k P,prunedOrdinaryFunction k s P N α)=ordinaryPruningMoment k s P N := by
  unfold prunedOrdinaryFunction ordinaryPruningMoment ordinaryPruning
  rw [integral_indicator (rectangleCoreGlobal_measurable k P N).compl,
    Measure.restrict_restrict (rectangleCoreGlobal_measurable k P N).compl,Set.inter_comm]
  rfl

theorem normalizedPruningModelMass_nonneg (k s N : ℕ) : 0≤normalizedPruningModelMass k s N :=
  tsum_nonneg (fun q=>mul_nonneg (completeCoefficient_nonneg k s q)
    (integral_nonneg (fun _=>pow_nonneg (norm_nonneg _) s)))

/-- A genuine bound on the ordinary pruning integral, with the exact model
tail and an actual half-power error. -/
theorem ordinary_pruning_moment_bound (k s : ℕ) (hk : 2≤k) (hs : 11≤s)
    (hks : k<s) (hsum : Summable (completeCoefficient k s)) :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P → ∀ N : ℕ,
      ordinaryPruningMoment k s P N ≤
        (2*(2 : ℝ)^(s-1))*(P^(s-k)*normalizedPruningModelMass k s N+C^s*P^((s : ℝ)-k-1/2)) := by
  obtain ⟨C,hC,hbound⟩ := ordinary_pruned_arc_sum_bound k s hk hs hks hsum
  refine ⟨C,hC,?_⟩
  intro P hP N
  have hPpos := zero_lt_one.trans_le hP
  have hδ := (broadArcWidth_pos (by omega : 1≤k) hPpos).le
  have hl := periodicMajorRegion_lintegral_le_of_integrable (broadDenominators P) hδ
    (prunedOrdinaryFunction_integrableOn k s P N) (prunedOrdinaryFunction_periodic k s P N)
    (prunedOrdinaryFunction_nonneg k s P N)
  change (∫⁻ x in ordinaryBroadMajor k P,ENNReal.ofReal (prunedOrdinaryFunction k s P N x))≤_ at hl
  have hi : IntegrableOn (prunedOrdinaryFunction k s P N) (ordinaryBroadMajor k P) :=
    (prunedOrdinaryFunction_integrableOn k s P N 0 1).mono_set
      ((ordinaryBroadMajor_subset k P).trans Set.Ioc_subset_Icc_self)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (prunedOrdinaryFunction_nonneg k s P N)),integral_prunedOrdinaryFunction] at hl
  have hb := hbound P hP N (broadDenominators P) (fun q hq=>(mem_broadDenominators P q).mp hq)
  have hle := hl.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ)≤2)))
  have hnn : 0≤2*((2 : ℝ)^(s-1)*(P^(s-k)*normalizedPruningModelMass k s N+C^s*P^((s : ℝ)-k-1/2))) := by
    have := normalizedPruningModelMass_nonneg k s N
    positivity
  exact ((ENNReal.ofReal_le_ofReal_iff hnn).mp hle).trans_eq (by ring)

theorem ordinary_pruning_moment_isLittleO (k s : ℕ) (hk : 2≤k) (hs : 11≤s)
    (hks : k<s) (hsum : Summable (completeCoefficient k s))
    (P : ℕ→ℝ) (N : ℕ→ℕ) (hP : Tendsto P atTop atTop) (hN : Tendsto N atTop atTop) :
    (fun n=>ordinaryPruningMoment k s (P n) (N n))=o[atTop](fun n=>(P n)^(s-k)) := by
  obtain ⟨C,hC,hbound⟩ := ordinary_pruning_moment_bound k s hk hs hks hsum
  have hp1 : ∀ᶠ n in atTop,1≤P n := hP.eventually_ge_atTop 1
  apply (isLittleO_iff_tendsto' (hp1.mono (fun n hn hzero=>by
    have hp : 0<P n := zero_lt_one.trans_le hn
    exact False.elim ((pow_ne_zero _ hp.ne') hzero)))).mpr
  have htail := (normalizedPruningModelMass_tendsto_zero k s (by omega) hks hsum).comp hN
  have herr := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/2)).comp hP).const_mul (C^s)
  have hlim : Tendsto (fun n=>(2*(2 : ℝ)^(s-1))*(normalizedPruningModelMass k s (N n)+
      C^s*(P n)^(-(1/2 : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (htail.add herr).const_mul (2*(2 : ℝ)^(s-1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [hp1] with n hn
    exact div_nonneg (ordinaryPruningMoment_nonneg k s (P n) (N n)) (pow_nonneg (by linarith) _)
  · filter_upwards [hp1] with n hn
    have hp : 0<P n := zero_lt_one.trans_le hn
    apply (div_le_iff₀ (pow_pos hp (s-k))).mpr
    have hb := hbound (P n) hn (N n)
    have he : (P n)^((s : ℝ)-k-1/2)=(P n)^(s-k)*(P n)^(-(1/2 : ℝ)) := by
      rw [← Real.rpow_natCast,← Real.rpow_add hp,Nat.cast_sub hks.le]
      congr 1
    exact hb.trans_eq (by rw [he]; ring)

theorem degree8_ordinary_pruning12_isLittleO (P : ℕ→ℝ) (N : ℕ→ℕ)
    (hP : Tendsto P atTop atTop) (hN : Tendsto N atTop atTop) :
    (fun n=>ordinaryPruningMoment 8 12 (P n) (N n))=o[atTop](fun n=>(P n)^4) :=
  ordinary_pruning_moment_isLittleO 8 12 (by norm_num) (by norm_num) (by norm_num)
    (degree8_completeCoefficient_summable 12 (by norm_num)) P N hP hN

theorem degree9_ordinary_pruning11_isLittleO (P : ℕ→ℝ) (N : ℕ→ℕ)
    (hP : Tendsto P atTop atTop) (hN : Tendsto N atTop atTop) :
    (fun n=>ordinaryPruningMoment 9 11 (P n) (N n))=o[atTop](fun n=>(P n)^2) :=
  ordinary_pruning_moment_isLittleO 9 11 (by norm_num) (by norm_num) (by norm_num)
    (degree9_completeCoefficient_summable 11 (by norm_num)) P N hP hN

#print axioms ordinary_pruned_arc_sum_bound
#print axioms degree8_ordinary_pruning12_isLittleO
#print axioms degree9_ordinary_pruning11_isLittleO

end Waring.EndgameCompletion
