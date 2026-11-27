import Waring.PolicyCompletionCartesian

/-!
# Actual next-stage domains inside the Cartesian terminal family

The next centered-difference phase carries a new height and coefficient,
and doubles every old height. Keeping those variables gives an injective
map into a Cartesian family. Domain enlargement is then justified by exact
Fourier collision counts, never by pointwise subsum norm comparisons.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionNextDomain
open PolicyCompletionCartesian PolicyCompletionGoodRecurrence PolicyCompletionGoodBranch
open SeedCompletionBackwardCount SeedCompletionBackwardMoments SeedCompletionBackwardAggregate
open IntegerDifferencePolynomial PolicyCompletionHolder SmoothMoments

abbrev IntegerLabel (j : ℕ) := (Fin j → ℤ) × (Fin j → ℤ)
abbrev NextLabel (j : ℕ) := Σ _ : IntegerLabel j × ℕ, ℤ × ℤ

/-- The two original integer arrays are retained without quotienting or
multiplicity loss. -/
def nextArrayEncode {j : ℕ} (p : NextLabel j) : IntegerLabel (j+1) × ℤ :=
  ((Fin.cons p.2.2 (fun i => 2*p.1.1.1 i),
    Fin.cons (p.1.2 : ℤ) p.1.1.2),p.2.1)

def nextArrayDecode {j : ℕ} (p : IntegerLabel (j+1) × ℤ) : NextLabel j :=
  ⟨((fun i => p.1.1 i.succ/2,fun i => p.1.2 i.succ),(p.1.2 0).toNat),
    (p.2,p.1.1 0)⟩

theorem nextArrayEncode_injective {j : ℕ} : Function.Injective (@nextArrayEncode j) := by
  have hleft : Function.LeftInverse (@nextArrayDecode j) (@nextArrayEncode j) := by
    intro p
    rcases p with ⟨⟨⟨h,m⟩,w⟩,⟨x,t⟩⟩
    simp [nextArrayDecode,nextArrayEncode]
  exact hleft.injective

theorem integerParameters_next {j : ℕ} (h m : Fin j → ℤ) (t w : ℤ) :
    integerParameters (Fin.cons t (fun i => 2*h i)) (Fin.cons w m) =
      (t,w) :: doubleHeights (integerParameters h m) := by
  simp [integerParameters,List.ofFn_succ,doubleHeights,List.map_ofFn,Function.comp_def]

theorem nextArrayEncode_frequency {j : ℕ} (k : ℕ) (p : NextLabel j) :
    arrayPhase k (nextArrayEncode p) =
      aggregateNextPhase k (fun c : IntegerLabel j × ℕ => integerParameters c.1.1 c.1.2)
        (fun c => (c.2 : ℤ)) p := by
  simp only [arrayPhase,nextArrayEncode,integerParameters_next,
    aggregateNextPhase,nextIntegerPhase]

def nextHeightSet {j : ℕ} (H : Finset (Fin j → ℤ)) (T : ℤ) :
    Finset (Fin (j+1) → ℤ) := by
  classical
  exact (Finset.Icc 1 T ×ˢ H).image (fun p => Fin.cons p.1 (fun i => 2*p.2 i))

def nextCoefficientSets {j : ℕ} (W : Finset ℕ) (C : Fin j → Finset ℤ) :
    Fin (j+1) → Finset ℤ := by
  classical
  exact Fin.cons (W.image (fun w : ℕ => (w : ℤ))) C

/-- The variable-dependent height range is enlarged to one common interval;
the center range `[2,2N]` is enlarged to the source interval `[1,2N]`. -/
theorem nextArrayEncode_image_subset {j : ℕ} (k : ℕ)
    (H : Finset (Fin j → ℤ)) (C : Fin j → Finset ℤ) (W : Finset ℕ) (N T : ℤ)
    (hT : ∀ w ∈ W, N/(w : ℤ)^k ≤ T) :
    (aggregateNextDomain (integerCartesian H C ×ˢ W) (fun c => (c.2 : ℤ)) N k).image
      nextArrayEncode ⊆
      integerCartesian (nextHeightSet H T) (nextCoefficientSets W C) ×ˢ Finset.Icc 1 (2*N) := by
  classical
  intro x hx
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  rcases Finset.mem_sigma.mp hp with ⟨hc,hp⟩
  have hold := Finset.mem_product.mp (Finset.mem_product.mp hc).1
  have hw := (Finset.mem_product.mp hc).2
  rcases Finset.mem_product.mp hp with ⟨hcenter,hheight⟩
  rcases Finset.mem_Icc.mp hcenter with ⟨hxlo,hxhi⟩
  rcases Finset.mem_Icc.mp hheight with ⟨htlo,hthi⟩
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,
    Finset.mem_Icc.mpr ⟨by change 1 ≤ p.2.1; omega,hxhi⟩⟩
  · exact Finset.mem_image.mpr ⟨(p.2.2,p.1.1.1),Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨htlo,hthi.trans (hT p.1.2 hw)⟩,hold.1⟩,rfl⟩
  · apply Fintype.mem_piFinset.mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Finset.mem_image_of_mem _ hw
    · exact Fintype.mem_piFinset.mp hold.2 i

/-- Expanding the unchanged short smooth tuple gives the actual doubled
one-variable frequency, with its original smooth support. -/
theorem nextSmoothMoment_eq_mixed {κ : Type*} (k s : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (W : Finset ℕ) (N : ℤ) (Q R : ℝ) :
    nextSmoothMoment k s C params W N Q R =
      mixedFrequencyEvenMoment
        (aggregateNextDomain (C ×ˢ W) (fun c => (c.2 : ℤ)) N k)
        (aggregateNextPhase k (fun c => params c.1) (fun c => (c.2 : ℤ))) 1
        (smoothNumbers Q R) (fun n => (2 : ℤ)^k*(n : ℤ)^k) s := by
  unfold nextSmoothMoment
  rw [aggregateNextMoment_eq_product_integral]
  have hsum (α : ℝ) :
      (∑ u ∈ finiteTuples (smoothNumbers Q R) s,
        fourier ((2 : ℤ)^k*smoothTupleValue k s u) (α : AddCircle (1 : ℝ))) =
      (∑ n ∈ smoothNumbers Q R, fourier ((2 : ℤ)^k*(n : ℤ)^k)
        (α : AddCircle (1 : ℝ)))^s := by
    rw [sum_pow_fourier]
    simp only [smoothTupleValue,Finset.mul_sum]
  simp_rw [hsum,norm_pow,← pow_mul]
  simp only [mixedFrequencyEvenMoment,mul_one,Nat.mul_comm s 2]

/-- The exact next-stage moment is bounded by the actual Cartesian mixed
moment after injective reindexing and finite-domain enlargement. -/
theorem nextSmoothMoment_le_cartesian {j : ℕ} (k s : ℕ)
    (H : Finset (Fin j → ℤ)) (C : Fin j → Finset ℤ) (W : Finset ℕ) (N T : ℤ)
    (Q R : ℝ) (hT : ∀ w ∈ W, N/(w : ℤ)^k ≤ T) :
    nextSmoothMoment k s (integerCartesian H C)
      (fun c => integerParameters c.1 c.2) W N Q R ≤
      cartesianMixedMoment k s (nextHeightSet H T) (nextCoefficientSets W C)
        1 (2*N) (smoothNumbers Q R) (fun n => (2 : ℤ)^k*(n : ℤ)^k) := by
  rw [nextSmoothMoment_eq_mixed]
  have hfreq : aggregateNextPhase k
      (fun c : IntegerLabel j × ℕ => integerParameters c.1.1 c.1.2)
      (fun c => (c.2 : ℤ)) = fun p => arrayPhase k (nextArrayEncode p) := by
    funext p
    exact (nextArrayEncode_frequency k p).symm
  rw [hfreq,← mixedFrequencyEvenMoment_image_left _ nextArrayEncode
    nextArrayEncode_injective]
  exact mixedFrequencyEvenMoment_mono (nextArrayEncode_image_subset k H C W N T hT)
    (Finset.Subset.refl _) (arrayPhase k) 1 _ s

/-- Injective relabeling of the second finite sum preserves its full mixed
moment exactly. -/
theorem mixedMoment_image_right {α β γ : Type*} [DecidableEq γ]
    (A : Finset α) (f : α → ℤ) (p : ℕ) (B : Finset β)
    (e : β → γ) (he : Function.Injective e) (g : γ → ℤ) (s : ℕ) :
    mixedFrequencyEvenMoment A f p (B.image e) g s =
      mixedFrequencyEvenMoment A f p B (fun n => g (e n)) s := by
  classical
  unfold mixedFrequencyEvenMoment
  have hsum (α : ℝ) : (∑ n ∈ B.image e, fourier (g n) (α : AddCircle (1 : ℝ))) =
      ∑ n ∈ B, fourier (g (e n)) (α : AddCircle (1 : ℝ)) :=
    Finset.sum_image (fun _ _ _ _ heq => he heq)
  simp_rw [hsum]

/-- Doubling a positive R-smooth integer preserves smoothness when R>=2,
and doubles the literal length cutoff. -/
theorem double_smooth_mem {Q R : ℝ} (hQ : 0 ≤ Q) (hR : 2 ≤ R)
    {n : ℕ} (hn : n ∈ smoothNumbers Q R) : 2*n ∈ smoothNumbers (2*Q) R := by
  rcases mem_smoothNumbers.mp hn with ⟨⟨hn1,hnQ⟩,hsmooth⟩
  have hnR : (n : ℝ) ≤ Q :=
    (by exact_mod_cast hnQ : (n : ℝ) ≤ ⌊Q⌋₊).trans (Nat.floor_le hQ)
  apply mem_smoothNumbers.mpr
  refine ⟨⟨by omega,Nat.le_floor ?_⟩,?_⟩
  · push_cast
    nlinarith
  · intro q hq hqn
    rcases hq.dvd_mul.mp hqn with hq2 | hqn
    · have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2
      exact (by exact_mod_cast hqle : (q : ℝ) ≤ 2).trans hR
    · exact hsmooth q hq hqn

/-- After doubling the short smooth variables, the next moment is bounded
by an ordinary full smooth mixed moment on the enlarged Cartesian domain. -/
theorem nextSmoothMoment_le_cartesian_smooth {j : ℕ} (k s : ℕ)
    (H : Finset (Fin j → ℤ)) (C : Fin j → Finset ℤ) (W : Finset ℕ) (N T : ℤ)
    (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 2 ≤ R)
    (hT : ∀ w ∈ W, N/(w : ℤ)^k ≤ T) :
    nextSmoothMoment k s (integerCartesian H C)
      (fun c => integerParameters c.1 c.2) W N Q R ≤
      cartesianMixedMoment k s (nextHeightSet H T) (nextCoefficientSets W C)
        1 (2*N) (smoothNumbers (2*Q) R) (fun n => (n : ℤ)^k) := by
  have h := nextSmoothMoment_le_cartesian k s H C W N T Q R hT
  apply h.trans
  unfold cartesianMixedMoment
  have hfreq : (fun n : ℕ => (2 : ℤ)^k*(n : ℤ)^k) =
      fun n : ℕ => ((2*n : ℕ) : ℤ)^k := by
    funext n
    simp only [Nat.cast_mul,Nat.cast_ofNat,mul_pow]
  rw [hfreq,← mixedMoment_image_right _ _ _ (smoothNumbers Q R)
    (fun n : ℕ => 2*n) (fun x y hxy => by change 2*x=2*y at hxy; omega)
    (fun n : ℕ => (n : ℤ)^k) s]
  exact mixedFrequencyEvenMoment_mono (Finset.Subset.refl _) (by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact double_smooth_mem hQ hR hm) _ 1 _ s

theorem nextCoefficientSets_nonzero {j : ℕ} (W : Finset ℕ) (C : Fin j → Finset ℤ)
    (hw : ∀ w ∈ W, 0 < w) (hm : ∀ i, ∀ m ∈ C i, m ≠ 0) :
    ∀ i, ∀ m ∈ nextCoefficientSets W C i, m ≠ 0 := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro m hm
    obtain ⟨w,hwW,rfl⟩ := Finset.mem_image.mp hm
    exact_mod_cast (hw w hwW).ne'
  · exact hm i

/-- Final source interface: the literal next moment is bounded by the
integral of the existing Cartesian polynomialFamily and the ordinary
smooth Weyl sum. All domain comparisons have been proved by counts. -/
theorem nextSmoothMoment_le_cartesian_integral {j : ℕ} (k s : ℕ)
    (H : Finset (Fin j → ℤ)) (C : Fin j → Finset ℤ) (W : Finset ℕ) (N T : ℤ)
    (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 2 ≤ R)
    (hT : ∀ w ∈ W, N/(w : ℤ)^k ≤ T)
    (hw : ∀ w ∈ W, 0 < w) (hm : ∀ i, ∀ m ∈ C i, m ≠ 0) :
    nextSmoothMoment k s (integerCartesian H C)
      (fun c => integerParameters c.1 c.2) W N Q R ≤
      ∫ α in (0 : ℝ)..1,
        ‖PolynomialSumReduction.polynomialFamily k
          (CartesianPolynomialBounds.cartesianParameters
            (castHeightSet (nextHeightSet H T)) (castCoefficientSets (nextCoefficientSets W C)))
          Prod.fst Prod.snd α 1 (2*N)‖^2 * ‖smoothWeyl k (2*Q) R α‖^(2*s) := by
  have h := nextSmoothMoment_le_cartesian_smooth k s H C W N T Q R hQ hR hT
  rw [cartesianMixedMoment_eq_integral _ _ _ _ _ _ _ _
    (nextCoefficientSets_nonzero W C hw hm)] at h
  have heq (α : ℝ) : frequencySum (smoothNumbers (2*Q) R) (fun n => (n : ℤ)^k) α =
      smoothWeyl k (2*Q) R α := by
    simp only [frequencySum,smoothWeyl,phase_eq_fourier,Nat.cast_pow]
  simpa only [heq] using h

#print axioms nextArrayEncode_injective
#print axioms nextSmoothMoment_le_cartesian
#print axioms nextSmoothMoment_le_cartesian_integral
end Waring.PolicyCompletionNextDomain
