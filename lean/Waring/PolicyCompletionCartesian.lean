import Waring.PolicyCompletionGoodRecurrence
import Waring.PolicyCompletionEndpointPartition
import Waring.CartesianPolynomialBounds

/-!
# The exact integer-frequency interface to Cartesian source polynomials

The recurrence's integer polynomial is the same modified centered phase
used by the existing Cartesian terminal bounds. All changes of labels in
this module are injective casts and exact finite-sum identities.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionCartesian
open IntegerDifferencePolynomial PolynomialSumReduction CartesianPolynomialBounds
open PolicyCompletionHolder PolicyCompletionEndpointPartition
open SeedCompletionBackwardMoments

def integerParameters {j : ℕ} (h m : Fin j → ℤ) : List (ℤ × ℤ) :=
  List.ofFn (fun i => (h i,m i))

def castTuple {j : ℕ} (h : Fin j → ℤ) : Fin j → ℝ := fun i => (h i : ℝ)

theorem castTuple_injective {j : ℕ} : Function.Injective (@castTuple j) := by
  intro h g heq
  funext i
  exact Int.cast_injective (congrFun heq i)

theorem realParameters_integerParameters {j : ℕ} (h m : Fin j → ℤ) :
    realParameters (integerParameters h m)=parameters (castTuple h) (castTuple m) := by
  simp [realParameters,integerParameters,parameters,castTuple,List.map_ofFn,Function.comp_def]

theorem integerParameters_coefficient_ne_zero {j : ℕ} (h m : Fin j → ℤ)
    (hm : ∀ i, m i ≠ 0) : ∀ p ∈ integerParameters h m, p.2 ≠ 0 := by
  simpa only [integerParameters,List.forall_mem_ofFn_iff] using hm

def arrayPhase {j : ℕ} (k : ℕ) (x : ((Fin j → ℤ) × (Fin j → ℤ)) × ℤ) : ℤ :=
  (powerPolynomial k (integerParameters x.1.1 x.1.2)).eval x.2

/-- Every finite integer-array family has exactly the Fourier frequencies
used by the literal modified centered source polynomial. -/
theorem polynomialFamily_integer_frequency {ι : Type*} {j : ℕ}
    (k : ℕ) (B : Finset ι) (h m : ι → Fin j → ℤ) (α : ℝ) (a b : ℤ)
    (hm : ∀ c ∈ B, ∀ i, m c i ≠ 0) :
    polynomialFamily k B (fun c => castTuple (h c)) (fun c => castTuple (m c)) α a b =
      frequencySum (B ×ˢ Finset.Icc a b)
        (fun p => (powerPolynomial k (integerParameters (h p.1) (m p.1))).eval p.2) α := by
  classical
  simp only [polynomialFamily,UnseparatedDifferencing.familySum,frequencySum,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro z hz
  rw [← realParameters_integerParameters,← powerPolynomial_eval_int k _
    (integerParameters_coefficient_ne_zero _ _ (hm c hc)) z]
  exact exp_linear_eq_fourier α _

def integerCartesian {j : ℕ} (H : Finset (Fin j → ℤ)) (C : Fin j → Finset ℤ) :
    Finset ((Fin j → ℤ) × (Fin j → ℤ)) := H ×ˢ Fintype.piFinset C

def castHeightSet {j : ℕ} (H : Finset (Fin j → ℤ)) : Finset (Fin j → ℝ) := by
  classical
  exact H.image castTuple

def castCoefficientSets {j : ℕ} (C : Fin j → Finset ℤ) : Fin j → Finset ℝ := by
  classical
  exact fun i => (C i).image (fun z : ℤ => (z : ℝ))

theorem cast_cartesian_eq_image {j : ℕ} (H : Finset (Fin j → ℤ))
    (C : Fin j → Finset ℤ) :
    cartesianParameters (castHeightSet H) (castCoefficientSets C) =
      (integerCartesian H C).image (Prod.map castTuple castTuple) := by
  classical
  change H.image castTuple ×ˢ
    Fintype.piFinset (fun i => (C i).image (fun z : ℤ => (z : ℝ))) =
      (H ×ˢ Fintype.piFinset C).image (Prod.map castTuple castTuple)
  rw [Fintype.piFinset_image,Finset.prodMap_image_product]
  rfl

theorem castParameter_injective {j : ℕ} :
    Function.Injective (Prod.map (@castTuple j) (@castTuple j)) := by
  intro x y hxy
  exact Prod.ext (castTuple_injective (congrArg Prod.fst hxy))
    (castTuple_injective (congrArg Prod.snd hxy))

theorem polynomialFamily_castCartesian {j : ℕ} (k : ℕ)
    (H : Finset (Fin j → ℤ)) (C : Fin j → Finset ℤ) (α : ℝ) (a b : ℤ) :
    polynomialFamily k (cartesianParameters (castHeightSet H) (castCoefficientSets C))
      Prod.fst Prod.snd α a b =
    polynomialFamily k (integerCartesian H C)
      (fun p => castTuple p.1) (fun p => castTuple p.2) α a b := by
  classical
  simp only [polynomialFamily,UnseparatedDifferencing.familySum,cast_cartesian_eq_image]
  rw [Finset.sum_image (fun _ _ _ _ heq => castParameter_injective heq)]
  rfl

/-- Exact Cartesian sum transport, valid at every differencing depth. -/
theorem cartesianFamily_eq_frequencySum {j : ℕ} (k : ℕ)
    (H : Finset (Fin j → ℤ)) (C : Fin j → Finset ℤ) (α : ℝ) (a b : ℤ)
    (hm : ∀ i, ∀ m ∈ C i, m ≠ 0) :
    polynomialFamily k (cartesianParameters (castHeightSet H) (castCoefficientSets C))
      Prod.fst Prod.snd α a b =
      frequencySum (integerCartesian H C ×ˢ Finset.Icc a b) (arrayPhase k) α := by
  rw [polynomialFamily_castCartesian]
  exact polynomialFamily_integer_frequency k (integerCartesian H C) Prod.fst Prod.snd α a b
    (fun c hc i => hm i _ (Fintype.mem_piFinset.mp (Finset.mem_product.mp hc).2 i))

/-- The moment on which Cartesian terminal estimates act, retaining the
actual integer coefficient and height domains. -/
def cartesianMixedMoment {j : ℕ} {ι : Type*} (k s : ℕ)
    (H : Finset (Fin j → ℤ)) (C : Fin j → Finset ℤ) (a b : ℤ)
    (B : Finset ι) (g : ι → ℤ) : ℝ :=
  mixedFrequencyEvenMoment (integerCartesian H C ×ˢ Finset.Icc a b)
    (arrayPhase k) 1 B g s

theorem cartesianMixedMoment_eq_integral {j : ℕ} {ι : Type*} (k s : ℕ)
    (H : Finset (Fin j → ℤ)) (C : Fin j → Finset ℤ) (a b : ℤ)
    (B : Finset ι) (g : ι → ℤ) (hm : ∀ i, ∀ m ∈ C i, m ≠ 0) :
    cartesianMixedMoment k s H C a b B g =
      ∫ α in (0 : ℝ)..1,
        ‖polynomialFamily k
          (cartesianParameters (castHeightSet H) (castCoefficientSets C))
          Prod.fst Prod.snd α a b‖^2 * ‖frequencySum B g α‖^(2*s) := by
  unfold cartesianMixedMoment mixedFrequencyEvenMoment
  simp only [cartesianFamily_eq_frequencySum k H C _ a b hm,frequencySum,mul_one]

#print axioms cartesianFamily_eq_frequencySum
#print axioms cartesianMixedMoment_eq_integral
end Waring.PolicyCompletionCartesian
