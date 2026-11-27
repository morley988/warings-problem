import Waring.EndgameCompletionBroadArcs

/-! # Measurable periodic pruning and exact real-frequency tail scaling -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Waring.EndgameCompletion
open MixedEndgame RestrictedSmoothArcs

theorem wrappedRationalBand_lintegral_le_of_integrable (p : ArcLabel) {δ : ℝ} (hδ : 0≤δ)
    {F : ℝ→ℝ} (hF : ∀ a b : ℝ,IntegrableOn F (Set.Icc a b))
    (hper : Function.Periodic F 1) (hF0 : ∀ x,0≤F x) :
    (∫⁻ x in wrappedRationalBand (arcLabelRat p) δ,ENNReal.ofReal (F x))≤
      ENNReal.ofReal (2*arcLabelIntegral p F δ) := by
  let r := arcLabelRat p
  have hd : 0≤δ/(r.den : ℝ) := div_nonneg hδ (Nat.cast_nonneg _)
  have hend : (r : ℝ)-δ/(r.den : ℝ)≤r+δ/(r.den : ℝ) := by linarith
  have hbase : (∫⁻ x in rationalBand r δ,ENNReal.ofReal (F x))=
      ENNReal.ofReal (arcLabelIntegral p F δ) := by
    rw [arcLabelIntegral_eq p F hδ]
    symm
    exact ofReal_integral_eq_lintegral_ofReal
      (by rw [rationalBand_eq_Icc]; exact hF _ _) (Filter.Eventually.of_forall hF0)
  have hshift : (∫⁻ x in Set.Icc ((r : ℝ)-δ/(r.den : ℝ)+1) ((r : ℝ)+δ/(r.den : ℝ)+1),
      ENNReal.ofReal (F x))=ENNReal.ofReal (arcLabelIntegral p F δ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hF _ _) (Filter.Eventually.of_forall hF0),
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (add_le_add_right hend 1),
      periodic_interval_translate hper,intervalIntegral.integral_of_le hend,
      ← integral_Icc_eq_integral_Ioc,← rationalBand_eq_Icc,← arcLabelIntegral_eq p F hδ]
  have hnonneg : 0≤arcLabelIntegral p F δ := by
    rw [arcLabelIntegral_eq p F hδ]
    exact integral_nonneg hF0
  calc
    _ ≤ (∫⁻ x in rationalBand r δ,ENNReal.ofReal (F x))+
        ∫⁻ x in Set.Icc ((r : ℝ)-δ/(r.den : ℝ)+1) ((r : ℝ)+δ/(r.den : ℝ)+1),
          ENNReal.ofReal (F x) := lintegral_union_le _ _ _
    _ = _ := by rw [hbase,hshift,← ENNReal.ofReal_add hnonneg hnonneg]; congr 1; ring

theorem periodicMajorRegion_lintegral_le_of_integrable (S : Finset ℕ+) {δ : ℝ} (hδ : 0≤δ)
    {F : ℝ→ℝ} (hF : ∀ a b : ℝ,IntegrableOn F (Set.Icc a b))
    (hper : Function.Periodic F 1) (hF0 : ∀ x,0≤F x) :
    (∫⁻ x in periodicMajorRegion S δ,ENNReal.ofReal (F x))≤
      ENNReal.ofReal (2*∑ q∈S,rationalArcSum (q : ℕ) F δ) := by
  let A := denominatorArcLabels S
  calc
    _ ≤ ∫⁻ x in ⋃ p∈A,wrappedRationalBand (arcLabelRat p) δ,ENNReal.ofReal (F x) :=
      lintegral_mono_set Set.inter_subset_right
    _ ≤ ∑ p∈A,∫⁻ x in wrappedRationalBand (arcLabelRat p) δ,ENNReal.ofReal (F x) :=
      lintegral_finset_union_le A _ _
    _ ≤ ∑ p∈A,ENNReal.ofReal (2*arcLabelIntegral p F δ) :=
      Finset.sum_le_sum (fun p _=>wrappedRationalBand_lintegral_le_of_integrable p hδ hF hper hF0)
    _ = ENNReal.ofReal (∑ p∈A,2*arcLabelIntegral p F δ) :=
      (ENNReal.ofReal_sum_of_nonneg (fun p _=>by
        apply mul_nonneg (by norm_num)
        rw [arcLabelIntegral_eq p F hδ]
        exact integral_nonneg hF0)).symm
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 2
      simp only [A,denominatorArcLabels,Finset.sum_sigma,arcLabelIntegral,rationalArcSum]

/-- The periodic union of the fixed scaled-frequency rectangles. Its
denominators are strictly below N and its real-frequency radius is N. -/
def rectangleCoreGlobal (k : ℕ) (P : ℝ) (N : ℕ) : Set ℝ :=
  {α | ∃ q : ℕ+, (q : ℕ)<N ∧ ∃ a : (ZMod (q : ℕ))ˣ,∃ m : ℤ,
    |α-(((a : ZMod (q : ℕ)).val : ℝ)/(q : ℝ)+m)|≤(N : ℝ)/P^k}

theorem rectangleCoreGlobal_measurable (k : ℕ) (P : ℝ) (N : ℕ) :
    MeasurableSet (rectangleCoreGlobal k P N) := by
  unfold rectangleCoreGlobal
  simp only [Set.setOf_exists,Set.setOf_and]
  apply MeasurableSet.iUnion
  intro q
  apply (MeasurableSet.const _).inter
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro m
  exact (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet

theorem rectangleCoreGlobal_add_one (k : ℕ) (P : ℝ) (N : ℕ) (α : ℝ) :
    α+1∈rectangleCoreGlobal k P N ↔ α∈rectangleCoreGlobal k P N := by
  constructor
  · rintro ⟨q,hq,a,m,hm⟩
    refine ⟨q,hq,a,m-1,?_⟩
    convert hm using 1
    congr 1
    push_cast
    ring
  · rintro ⟨q,hq,a,m,hm⟩
    refine ⟨q,hq,a,m+1,?_⟩
    convert hm using 1
    congr 1
    push_cast
    ring

def prunedOrdinaryFunction (k s : ℕ) (P : ℝ) (N : ℕ) : ℝ→ℝ :=
  (rectangleCoreGlobal k P N)ᶜ.indicator (fun α=>‖ordinaryWeyl k P α‖^s)

theorem prunedOrdinaryFunction_nonneg (k s : ℕ) (P : ℝ) (N : ℕ) (α : ℝ) :
    0≤prunedOrdinaryFunction k s P N α := by
  apply Set.indicator_nonneg
  exact fun x _=>pow_nonneg (norm_nonneg _) s

theorem prunedOrdinaryFunction_integrableOn (k s : ℕ) (P : ℝ) (N : ℕ) (a b : ℝ) :
    IntegrableOn (prunedOrdinaryFunction k s P N) (Set.Icc a b) :=
  ((continuous_ordinary k P).norm.pow s).integrableOn_Icc.indicator
    (rectangleCoreGlobal_measurable k P N).compl

theorem prunedOrdinaryFunction_periodic (k s : ℕ) (P : ℝ) (N : ℕ) :
    Function.Periodic (prunedOrdinaryFunction k s P N) 1 := by
  classical
  intro α
  simp only [prunedOrdinaryFunction,Set.indicator_apply,Set.mem_compl_iff,
    rectangleCoreGlobal_add_one,periodic_ordinaryWeyl k P α]

def scaledTailSet (q k : ℕ) (P : ℝ) (N : ℕ) : Set ℝ :=
  {β : ℝ | N≤q ∨ (N : ℝ)< |β*P^k|}

theorem scaledTailSet_measurable (q k : ℕ) (P : ℝ) (N : ℕ) :
    MeasurableSet (scaledTailSet q k P N) :=
  (MeasurableSet.const _).union
    ((isOpen_lt continuous_const (continuous_id.mul continuous_const).abs).measurableSet)

theorem outside_rectangle_mem_scaledTail (k N : ℕ) {P : ℝ} (hP : 0<P)
    (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {β : ℝ}
    (hβ : (((a : ZMod q).val : ℝ)/q+β)∉rectangleCoreGlobal k P N) :
    β∈scaledTailSet q k P N := by
  by_cases hq : N≤q
  · exact Or.inl hq
  · right
    by_contra h
    have hle : |β*P^k|≤(N : ℝ) := le_of_not_gt h
    have hb : |β|≤(N : ℝ)/P^k := by
      apply (le_div_iff₀ (pow_pos hP k)).mpr
      simpa only [abs_mul,abs_of_pos (pow_pos hP k)] using hle
    apply hβ
    refine ⟨⟨q,NeZero.pos q⟩,Nat.lt_of_not_ge hq,a,0,?_⟩
    simpa only [PNat.mk_coe,Int.cast_zero,add_zero,add_sub_cancel_left] using hb

theorem scaled_monomial_tail_integral (q k s N : ℕ) (hks : k≤s) {P : ℝ} (hP : 0<P) :
    (∫ β in scaledTailSet q k P N,‖monomialIntegral k P β‖^s)=
      P^(s-k)*(∫ γ in {γ : ℝ | N≤q ∨ (N : ℝ)< |γ|},‖monomialIntegral k 1 γ‖^s) := by
  classical
  let T := {γ : ℝ | N≤q ∨ (N : ℝ)< |γ|}
  have hT : MeasurableSet T := (MeasurableSet.const _).union
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have he (β : ℝ) : (scaledTailSet q k P N).indicator (fun x=>‖monomialIntegral k P x‖^s) β=
      P^s*T.indicator (fun γ=>‖monomialIntegral k 1 γ‖^s) (β*P^k) := by
    by_cases h : N≤q ∨ (N : ℝ)< |β*P^k|
    · simp only [Set.indicator_apply,scaledTailSet,T,Set.mem_setOf_eq,h,if_true]
      rw [monomialIntegral_scale k P,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hP,mul_pow]
    · simp only [Set.indicator_apply,scaledTailSet,T,Set.mem_setOf_eq,h,if_false,mul_zero]
  rw [← integral_indicator (scaledTailSet_measurable q k P N)]
  simp_rw [he]
  rw [integral_const_mul,MeasureTheory.Measure.integral_comp_mul_right
    (T.indicator (fun γ=>‖monomialIntegral k 1 γ‖^s)) (P^k),integral_indicator hT]
  simp only [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hP.le _)),smul_eq_mul]
  rw [show P^s=P^(s-k)*P^k by rw [← pow_add,Nat.sub_add_cancel hks]]
  field_simp
  rfl

#print axioms rectangleCoreGlobal_measurable
#print axioms scaled_monomial_tail_integral

end Waring.EndgameCompletion
