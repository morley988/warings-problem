import Waring.EndgameCompletionProductWeights

/-! # Literal product-weight representation integrals and their arc pieces -/

noncomputable section
open MeasureTheory Filter Asymptotics
open scoped BigOperators ENNReal Topology
namespace Waring.EndgameCompletion
open SmoothMoments ProductMultiplicity MixedEndgame

def productIntegrand (k u v L M n : ℕ) (α : ℝ) : ℂ :=
  ordinaryWeyl k ((M : ℝ)^L) α^u*productWeyl k L M α^v*
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))

def productArcContribution (k u v L M n : ℕ) (A : Set ℝ) : ℝ :=
  (∫ α in A,productIntegrand k u v L M n α).re

def productRepresentationIntegral (k u v L M n : ℕ) : ℂ :=
  ∫ α in (0 : ℝ)..1,productIntegrand k u v L M n α

def productPowerSum (k : ℕ) {u v L : ℕ}
    (x : (Fin u→ℕ)×(Fin v→Fin L→ℕ)) : ℕ :=
  (∑ i,(x.1 i)^k)+∑ j,(tupleProduct (x.2 j))^k

def productRepresentationSet (k u v L M n : ℕ) :=
  (mixedTuples (ordinaryNumbers ((M : ℝ)^L)) u (productBox L M) v).filter
    (fun x=>productPowerSum k x=n)

def productRepresentationCount (k u v L M n : ℕ) : ℕ :=
  (productRepresentationSet k u v L M n).card

theorem continuous_productIntegrand (k u v L M n : ℕ) :
    Continuous (productIntegrand k u v L M n) :=
  (((continuous_ordinary k ((M : ℝ)^L)).pow u).mul
    ((continuous_productWeyl k L M).pow v)).mul
    ((fourier (-(n : ℤ))).continuous.comp (AddCircle.continuous_mk' 1))

theorem productWeyl_product_expansion (k u v L M : ℕ) (α : ℝ) :
    ordinaryWeyl k ((M : ℝ)^L) α^u*productWeyl k L M α^v=
      ∑ x∈mixedTuples (ordinaryNumbers ((M : ℝ)^L)) u (productBox L M) v,
        fourier ((productPowerSum k x : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
  unfold ordinaryWeyl productWeyl
  simp_rw [phase_eq_fourier]
  simpa only [mixedFrequency,productPowerSum,Nat.cast_add,Nat.cast_sum] using
    product_sum_powers_fourier (ordinaryNumbers ((M : ℝ)^L))
      (fun x=>((x^k : ℕ) : ℤ)) u (productBox L M)
      (fun x=>((tupleProduct x^k : ℕ) : ℤ)) v (α : AddCircle (1 : ℝ))

theorem productIntegral_eq_count (k u v L M n : ℕ) :
    productRepresentationIntegral k u v L M n=(productRepresentationCount k u v L M n : ℂ) := by
  unfold productRepresentationIntegral productIntegrand
  simp_rw [productWeyl_product_expansion]
  simpa only [productRepresentationCount,productRepresentationSet,Nat.cast_inj] using
    interval_integral_finite_frequency_coefficient
      (mixedTuples (ordinaryNumbers ((M : ℝ)^L)) u (productBox L M) v)
      (fun x=>((productPowerSum k x : ℕ) : ℤ)) (n : ℤ)

theorem productIntegral_re_eq_count (k u v L M n : ℕ) :
    (productRepresentationIntegral k u v L M n).re=(productRepresentationCount k u v L M n : ℝ) := by
  rw [productIntegral_eq_count]
  simp

theorem mem_productRepresentationSet {k u v L M n : ℕ}
    {x : (Fin u→ℕ)×(Fin v→Fin L→ℕ)} :
    x∈productRepresentationSet k u v L M n ↔
      (∀ i,x.1 i∈ordinaryNumbers ((M : ℝ)^L)) ∧
      (∀ j,x.2 j∈productBox L M) ∧ productPowerSum k x=n := by
  simp only [productRepresentationSet,Finset.mem_filter,mixedTuples,Finset.mem_product,
    finiteTuples,Fintype.mem_piFinset,and_assoc]

theorem representable_of_product_count_pos {k u v L M n : ℕ}
    (h : 0<productRepresentationCount k u v L M n) : RepresentableByAtMost k (u+v) n := by
  obtain ⟨x,hx⟩ := Finset.card_pos.mp h
  rcases mem_productRepresentationSet.mp hx with ⟨ho,hp,hsum⟩
  refine ⟨u+v,le_rfl,Fin.append x.1 (fun j=>tupleProduct (x.2 j)),?_,?_⟩
  · intro i
    refine Fin.addCases (m := u) (n := v) ?_ ?_ i
    · intro j
      simpa only [Fin.append_left] using
        (show 0<x.1 j from (Finset.mem_Icc.mp (ho j)).1)
    · intro j
      have hh : ∀ l : Fin L,0<x.2 j l := fun l=>
        (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp (hp j)) l)).1
      simpa only [Fin.append_right,tupleProduct] using
        Finset.prod_pos (s := Finset.univ) (fun l _=>hh l)
  · rw [Fin.sum_univ_add]
    simpa only [Fin.append_left,Fin.append_right,productPowerSum] using hsum

theorem representable_of_product_integral_pos {k u v L M n : ℕ}
    (h : 0<(productRepresentationIntegral k u v L M n).re) :
    RepresentableByAtMost k (u+v) n := by
  rw [productIntegral_re_eq_count] at h
  exact representable_of_product_count_pos (by exact_mod_cast h)

theorem waringBound_of_eventually_product_integral_pos {k u v L : ℕ} (M : ℕ→ℕ)
    (h : ∀ᶠ n in atTop,0<(productRepresentationIntegral k u v L (M n) n).re) :
    WaringBound k (u+v) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  exact ⟨N,fun n hn=>representable_of_product_integral_pos (hN n hn)⟩

theorem productIntegral_partition (k u v L M n : ℕ)
    {core pruning minor : Set ℝ} (h : ArcPartition core pruning minor) :
    (productRepresentationIntegral k u v L M n).re=
      productArcContribution k u v L M n core+
        (productArcContribution k u v L M n pruning+productArcContribution k u v L M n minor) := by
  have hi : IntegrableOn (productIntegrand k u v L M n) (Set.Ioc 0 1) :=
    ((continuous_productIntegrand k u v L M n).intervalIntegrable 0 1).1
  have hsubA : core⊆Set.Ioc 0 1 := by rw [← h.cover]; exact Set.subset_union_left
  have hsubBC : pruning∪minor⊆Set.Ioc 0 1 := by rw [← h.cover]; exact Set.subset_union_right
  have hsubB : pruning⊆Set.Ioc 0 1 := Set.subset_union_left.trans hsubBC
  have hsubC : minor⊆Set.Ioc 0 1 := Set.subset_union_right.trans hsubBC
  unfold productRepresentationIntegral
  rw [intervalIntegral.integral_of_le zero_le_one,← h.cover,
    setIntegral_union (h.corePruning.union_right h.coreMinor)
      (h.measurablePruning.union h.measurableMinor) (hi.mono_set hsubA) (hi.mono_set hsubBC),
    setIntegral_union h.pruningMinor h.measurableMinor (hi.mono_set hsubB) (hi.mono_set hsubC),
    Complex.add_re,Complex.add_re]
  rfl

def absoluteProduct (k L M : ℕ) (α : ℝ) : ℝ≥0∞ := ENNReal.ofReal ‖productWeyl k L M α‖

def productArcMoment (k p L M : ℕ) (A : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ α,absoluteProduct k L M α^p ∂volume.restrict A

theorem productArcMoment_full (k p L M : ℕ) :
    productArcMoment k p L M (Set.Ioc 0 1)=ENNReal.ofReal (productMoment k p L M) := by
  unfold productArcMoment absoluteProduct productMoment
  rw [intervalIntegral.integral_of_le zero_le_one,
    ofReal_integral_eq_lintegral_ofReal
      (((continuous_productWeyl k L M).norm.pow p).intervalIntegrable 0 1).1
      (Filter.Eventually.of_forall (fun α=>pow_nonneg (norm_nonneg _) p))]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _)]

theorem productArcMoment_le_full (k p L M : ℕ) {A : Set ℝ} (hA : A⊆Set.Ioc 0 1) :
    productArcMoment k p L M A≤ENNReal.ofReal (productMoment k p L M) := by
  rw [← productArcMoment_full]
  exact lintegral_mono_set hA

theorem productIntegrand_norm (k u v L M n : ℕ) (α : ℝ) :
    ‖productIntegrand k u v L M n α‖=
      ‖ordinaryWeyl k ((M : ℝ)^L) α‖^u*‖productWeyl k L M α‖^v := by
  have hc : ‖fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))‖=1 := Circle.norm_coe _
  simp only [productIntegrand,norm_mul,norm_pow,hc,mul_one]

theorem productArcContribution_abs_le_lintegral (k u v L M n : ℕ) (A : Set ℝ) :
    ENNReal.ofReal |productArcContribution k u v L M n A|≤
      ∫⁻ α,absoluteOrdinary k ((M : ℝ)^L) α^u*absoluteProduct k L M α^v ∂volume.restrict A := by
  have h := (Complex.abs_re_le_norm (∫ α in A,productIntegrand k u v L M n α)).trans
    (norm_integral_le_lintegral_norm (μ := volume.restrict A) (productIntegrand k u v L M n))
  have h' := ENNReal.ofReal_le_of_le_toReal h
  simpa only [productArcContribution,productIntegrand_norm,
    ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _),ENNReal.ofReal_pow (norm_nonneg _),
    absoluteOrdinary,absoluteProduct] using h'

/-- Eventual positivity of the actual product integral follows from a
positive core and two negligible errors, and yields genuine Waring summands. -/
theorem waringBound_of_product_two_errors {k u v L : ℕ} (M : ℕ→ℕ)
    {main pruning minor scale : ℕ→ℝ} {c : ℝ} (hc : 0<c)
    (hscale : ∀ᶠ n in atTop,0<scale n)
    (hdecomp : ∀ᶠ n in atTop,(productRepresentationIntegral k u v L (M n) n).re=
      main n+(pruning n+minor n))
    (hmain : ∀ᶠ n in atTop,c*scale n≤main n)
    (hpruning : pruning=o[atTop]scale) (hminor : minor=o[atTop]scale) :
    WaringBound k (u+v) := by
  have he := (hpruning.add hminor).def (half_pos hc)
  apply waringBound_of_eventually_product_integral_pos M
  filter_upwards [hscale,hdecomp,hmain,he] with n hs hd hm herr
  have hb : |pruning n+minor n|≤c*scale n/2 := by
    simpa only [Real.norm_eq_abs,abs_of_pos hs,div_mul_eq_mul_div] using herr
  have hn := neg_abs_le (pruning n+minor n)
  have hcscale := mul_pos hc hs
  linarith

#print axioms productIntegral_eq_count
#print axioms representable_of_product_integral_pos
#print axioms waringBound_of_product_two_errors
end Waring.EndgameCompletion
