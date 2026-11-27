import Waring.EndgameCompletionArcMoments

/-!
# Literal periodic major regions and their actual moments

Reduced rational bands are represented with their endpoint translates
zero and one, and then intersected with the integration period (0,1].
The finite-union upper bound applies to every continuous nonnegative
periodic function; it does not require disjointness of the bands.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Waring.EndgameCompletion
open MixedEndgame RestrictedSmoothArcs

def wrappedRationalBand (r : ℚ) (δ : ℝ) : Set ℝ :=
  rationalBand r δ ∪ Set.Icc ((r : ℝ)-δ/(r.den : ℝ)+1) ((r : ℝ)+δ/(r.den : ℝ)+1)

def periodicMajorRegion (S : Finset ℕ+) (δ : ℝ) : Set ℝ :=
  Set.Ioc 0 1 ∩ ⋃ p∈denominatorArcLabels S, wrappedRationalBand (arcLabelRat p) δ

theorem wrappedRationalBand_measurable (r : ℚ) (δ : ℝ) : MeasurableSet (wrappedRationalBand r δ) :=
  (rationalBand_measurable r δ).union measurableSet_Icc

theorem periodicMajorRegion_measurable (S : Finset ℕ+) (δ : ℝ) :
    MeasurableSet (periodicMajorRegion S δ) := by
  apply measurableSet_Ioc.inter
  exact Finset.measurableSet_biUnion _ (fun p _=>wrappedRationalBand_measurable _ _)

theorem periodicMajorRegion_subset (S : Finset ℕ+) (δ : ℝ) :
    periodicMajorRegion S δ⊆Set.Ioc 0 1 := Set.inter_subset_left

theorem mem_periodicMajorRegion (S : Finset ℕ+) (δ x : ℝ) :
    x∈periodicMajorRegion S δ ↔ x∈Set.Ioc 0 1 ∧
      ∃ q∈S,∃ a : (ZMod (q : ℕ))ˣ,
        x∈wrappedRationalBand (arcLabelRat ⟨q,a⟩) δ := by
  simp only [periodicMajorRegion,Set.mem_inter_iff,Set.mem_iUnion,denominatorArcLabels,
    Finset.mem_sigma,Finset.mem_univ,and_true]
  constructor
  · rintro ⟨hx,⟨⟨q,a⟩,hq,hband⟩⟩
    exact ⟨hx,q,hq,a,hband⟩
  · rintro ⟨hx,q,hq,a,hband⟩
    exact ⟨hx,⟨q,a⟩,hq,hband⟩

theorem lintegral_finset_union_le {ι : Type*} (S : Finset ι) (A : ι→Set ℝ)
    (f : ℝ→ℝ≥0∞) : (∫⁻ x in ⋃ i∈S,A i,f x)≤∑ i∈S,∫⁻ x in A i,f x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have he : (⋃ j∈insert i S,A j)=A i∪⋃ j∈S,A j := by ext x; simp
    rw [he,Finset.sum_insert hi]
    exact (lintegral_union_le f _ _).trans (add_le_add_left ih _)

theorem periodic_interval_translate {F : ℝ→ℝ} (hper : Function.Periodic F 1) (a b : ℝ) :
    (∫ x in (a+1)..(b+1),F x)=∫ x in a..b,F x := by
  have hh := intervalIntegral.integral_comp_add_right (f := F) (a := a) (b := b) 1
  rw [show (fun x=>F (x+1))=F from funext hper] at hh
  exact hh.symm

theorem wrappedRationalBand_lintegral_le (p : ArcLabel) {δ : ℝ} (hδ : 0≤δ)
    {F : ℝ→ℝ} (hF : Continuous F) (hper : Function.Periodic F 1) (hF0 : ∀ x,0≤F x) :
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
      (by rw [rationalBand_eq_Icc]; exact hF.integrableOn_Icc)
      (Filter.Eventually.of_forall hF0)
  have hshift : (∫⁻ x in Set.Icc ((r : ℝ)-δ/(r.den : ℝ)+1) ((r : ℝ)+δ/(r.den : ℝ)+1),
      ENNReal.ofReal (F x))=ENNReal.ofReal (arcLabelIntegral p F δ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hF.integrableOn_Icc (Filter.Eventually.of_forall hF0),
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (add_le_add_right hend 1),
      periodic_interval_translate hper,
      intervalIntegral.integral_of_le hend,← integral_Icc_eq_integral_Ioc,
      ← rationalBand_eq_Icc,← arcLabelIntegral_eq p F hδ]
  have hnonneg : 0≤arcLabelIntegral p F δ := by
    rw [arcLabelIntegral_eq p F hδ]
    exact integral_nonneg hF0
  calc
    _ ≤ (∫⁻ x in rationalBand r δ,ENNReal.ofReal (F x))+
        ∫⁻ x in Set.Icc ((r : ℝ)-δ/(r.den : ℝ)+1) ((r : ℝ)+δ/(r.den : ℝ)+1),
          ENNReal.ofReal (F x) := lintegral_union_le _ _ _
    _ = _ := by rw [hbase,hshift,← ENNReal.ofReal_add hnonneg hnonneg]; congr 1; ring

/-- The actual integral on the wrapped union is bounded by twice the
literal unwrapped reduced-residue arc sum. -/
theorem periodicMajorRegion_lintegral_le (S : Finset ℕ+) {δ : ℝ} (hδ : 0≤δ)
    {F : ℝ→ℝ} (hF : Continuous F) (hper : Function.Periodic F 1) (hF0 : ∀ x,0≤F x) :
    (∫⁻ x in periodicMajorRegion S δ,ENNReal.ofReal (F x))≤
      ENNReal.ofReal (2*∑ q∈S,rationalArcSum (q : ℕ) F δ) := by
  let A := denominatorArcLabels S
  calc
    _ ≤ ∫⁻ x in ⋃ p∈A,wrappedRationalBand (arcLabelRat p) δ,ENNReal.ofReal (F x) :=
      lintegral_mono_set Set.inter_subset_right
    _ ≤ ∑ p∈A,∫⁻ x in wrappedRationalBand (arcLabelRat p) δ,ENNReal.ofReal (F x) :=
      lintegral_finset_union_le A _ _
    _ ≤ ∑ p∈A,ENNReal.ofReal (2*arcLabelIntegral p F δ) :=
      Finset.sum_le_sum (fun p _=>wrappedRationalBand_lintegral_le p hδ hF hper hF0)
    _ = ENNReal.ofReal (∑ p∈A,2*arcLabelIntegral p F δ) :=
      (ENNReal.ofReal_sum_of_nonneg (fun p _=>by
        apply mul_nonneg (by norm_num)
        rw [arcLabelIntegral_eq p F hδ]
        exact integral_nonneg hF0)).symm
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 2
      simp only [A,denominatorArcLabels,Finset.sum_sigma,arcLabelIntegral,rationalArcSum]

theorem periodicMajorRegion_integral_le (S : Finset ℕ+) {δ : ℝ} (hδ : 0≤δ)
    {F : ℝ→ℝ} (hF : Continuous F) (hper : Function.Periodic F 1) (hF0 : ∀ x,0≤F x) :
    (∫ x in periodicMajorRegion S δ,F x)≤2*∑ q∈S,rationalArcSum (q : ℕ) F δ := by
  have hh := periodicMajorRegion_lintegral_le S hδ hF hper hF0
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hF.integrableOn_Icc.mono_set ((periodicMajorRegion_subset S δ).trans Set.Ioc_subset_Icc_self))
    (Filter.Eventually.of_forall hF0)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun q _=>rationalArcSum_nonneg (q : ℕ) hδ hF0))).mp hh

def broadDenominators (P : ℝ) : Finset ℕ+ :=
  (Finset.Icc 1 ⌊P⌋₊).subtype (fun q : ℕ=>0<q)

theorem mem_broadDenominators (P : ℝ) (q : ℕ+) :
    q∈broadDenominators P ↔ (q : ℝ)≤P := by
  unfold broadDenominators
  change (⟨(q : ℕ),q.pos⟩ : {n : ℕ // 0<n})∈
    (Finset.Icc 1 ⌊P⌋₊).subtype (fun n : ℕ=>0<n) ↔ (q : ℝ)≤P
  rw [Finset.mem_subtype,Finset.mem_Icc]
  change (1≤(q : ℕ) ∧ (q : ℕ)≤⌊P⌋₊) ↔ (q : ℝ)≤P
  exact (and_iff_right (show 1≤(q : ℕ) from q.pos)).trans (Nat.le_floor_iff' q.ne_zero)

def ordinaryBroadMajor (k : ℕ) (P : ℝ) : Set ℝ :=
  periodicMajorRegion (broadDenominators P) (broadArcWidth k P)

theorem ordinaryBroadMajor_measurable (k : ℕ) (P : ℝ) : MeasurableSet (ordinaryBroadMajor k P) :=
  periodicMajorRegion_measurable _ _

theorem ordinaryBroadMajor_subset (k : ℕ) (P : ℝ) : ordinaryBroadMajor k P⊆Set.Ioc 0 1 :=
  periodicMajorRegion_subset _ _

theorem periodic_ordinaryWeyl (k : ℕ) (P : ℝ) : Function.Periodic (ordinaryWeyl k P) 1 := by
  intro x
  unfold ordinaryWeyl
  exact Finset.sum_congr rfl (fun n _=>periodic_phase k n x)

theorem ordinary_broad_major_moment_bound (k s : ℕ) (hk : 2≤k) (hs : 11≤s)
    (hks : k<s) (hsum : Summable (completeCoefficient k s)) :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P →
      ordinaryArcMoment k s P (ordinaryBroadMajor k P)≤ENNReal.ofReal (C*P^(s-k)) := by
  obtain ⟨D,hD,hbound⟩ := ordinary_broad_arc_sum_bound k s hk hs hks hsum
  let B := ordinaryMajorMomentConstant k s
  refine ⟨2*(2 : ℝ)^(s-1)*(|B|+D^s),by positivity,?_⟩
  intro P hP
  have hPpos := zero_lt_one.trans_le hP
  have hδ := (broadArcWidth_pos (by omega : 1≤k) hPpos).le
  have hper : Function.Periodic (fun α=>‖ordinaryWeyl k P α‖^s) 1 := by
    intro x
    dsimp only
    rw [periodic_ordinaryWeyl k P x]
  have hl := periodicMajorRegion_lintegral_le (broadDenominators P) hδ
    ((continuous_ordinary k P).norm.pow s) hper (fun x=>pow_nonneg (norm_nonneg _) s)
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _)] at hl
  change ordinaryArcMoment k s P (ordinaryBroadMajor k P)≤_ at hl
  have hb := hbound P hP (broadDenominators P)
    (fun q hq=>(mem_broadDenominators P q).mp hq)
  have hpow : P^((s : ℝ)-k-1/2)≤P^(s-k) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hP
    rw [Nat.cast_sub hks.le]
    linarith
  have hi : B*P^(s-k)+D^s*P^((s : ℝ)-k-1/2)≤(|B|+D^s)*P^(s-k) := by
    calc
      _ ≤ |B| *P^(s-k)+D^s*P^(s-k) := add_le_add
        (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity))
        (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = _ := by ring
  apply hl.trans (ENNReal.ofReal_le_ofReal _)
  calc
    _ ≤ 2*((2 : ℝ)^(s-1)*(B*P^(s-k)+D^s*P^((s : ℝ)-k-1/2))) := by gcongr
    _ ≤ 2*((2 : ℝ)^(s-1)*((|B|+D^s)*P^(s-k))) := by gcongr
    _ = _ := by ring

/-- The full ordinary twelfth moment on the actual degree-eight broad
major region is unconditional. -/
theorem degree8_ordinary_broad_major12 :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P →
      ordinaryArcMoment 8 12 P (ordinaryBroadMajor 8 P)≤ENNReal.ofReal (C*P^4) :=
  ordinary_broad_major_moment_bound 8 12 (by norm_num) (by norm_num) (by norm_num)
    (degree8_completeCoefficient_summable 12 (by norm_num))

/-- The full ordinary eleventh moment on the actual degree-nine broad
major region is unconditional. -/
theorem degree9_ordinary_broad_major11 :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P →
      ordinaryArcMoment 9 11 P (ordinaryBroadMajor 9 P)≤ENNReal.ofReal (C*P^2) :=
  ordinary_broad_major_moment_bound 9 11 (by norm_num) (by norm_num) (by norm_num)
    (degree9_completeCoefficient_summable 11 (by norm_num))

#print axioms periodicMajorRegion_lintegral_le
#print axioms periodicMajorRegion_integral_le
#print axioms degree8_ordinary_broad_major12
#print axioms degree9_ordinary_broad_major11

end Waring.EndgameCompletion
