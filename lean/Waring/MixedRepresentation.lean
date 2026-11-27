import Waring.MixedEvenMoments
import Waring.RepresentationIntegral
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Actual mixed ordinary/smooth representation integrals

The cutoff P is arbitrary. Ordinary variables run through 1,...,floor(P),
and smooth variables run through the actual positive R-smooth set with the
same cutoff. Orthogonality identifies the mixed integral with a finite count.
Every counted tuple supplies genuine positive natural summands. Consequently,
eventual positivity at any chosen P(n), R(n) implies the actual Waring bound.
No equality with the generous all-ordinary cutoff n is assumed or needed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Waring
open SmoothMoments

/-- Positive ordinary summands of length at most the real cutoff P. -/
def ordinaryNumbers (P : ℝ) : Finset ℕ := Finset.Icc 1 ⌊P⌋₊

/-- The ordinary Weyl sum with the same phase convention as the smooth sum. -/
def ordinaryWeyl (k : ℕ) (P α : ℝ) : ℂ :=
  ∑ x ∈ ordinaryNumbers P, phase k x α

/-- The natural-number sum of powers for an ordinary block and a smooth block. -/
def mixedPowerSum (k : ℕ) {u v : ℕ}
    (f : (Fin u → ℕ) × (Fin v → ℕ)) : ℕ :=
  (∑ i, (f.1 i)^k) + ∑ j, (f.2 j)^k

/-- Finite mixed representations at the stated length and smoothness cutoffs. -/
def mixedRepresentationSet (k u v : ℕ) (P R : ℝ) (n : ℕ) :
    Finset ((Fin u → ℕ) × (Fin v → ℕ)) :=
  (mixedTuples (ordinaryNumbers P) u (smoothNumbers P R) v).filter
    (fun f => mixedPowerSum k f = n)

def mixedRepresentationCount (k u v : ℕ) (P R : ℝ) (n : ℕ) : ℕ :=
  (mixedRepresentationSet k u v P R n).card

/-- The precise mixed circle-method integral in the two proposed endgames. -/
def mixedRepresentationIntegral (k u v : ℕ) (P R : ℝ) (n : ℕ) : ℂ :=
  ∫ α in (0 : ℝ)..1,
    ordinaryWeyl k P α ^ u * smoothWeyl k P R α ^ v *
      fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))

/-- Product expansion retains the two distinct summation sets and their cutoffs. -/
theorem mixedWeyl_product_expansion (k u v : ℕ) (P R α : ℝ) :
    ordinaryWeyl k P α ^ u * smoothWeyl k P R α ^ v =
      ∑ f ∈ mixedTuples (ordinaryNumbers P) u (smoothNumbers P R) v,
        fourier ((mixedPowerSum k f : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
  unfold ordinaryWeyl smoothWeyl
  simp_rw [phase_eq_fourier]
  simpa only [mixedFrequency, mixedPowerSum, Nat.cast_add, Nat.cast_sum] using
    (product_sum_powers_fourier (ordinaryNumbers P) (fun x => ((x^k : ℕ) : ℤ)) u
      (smoothNumbers P R) (fun x => ((x^k : ℕ) : ℤ)) v (α : AddCircle (1 : ℝ)))

/-- Exact coefficient extraction for arbitrary cutoffs and nonnegative numbers
of variables; no asymptotic estimate enters this identity. -/
theorem mixedIntegral_eq_count (k u v : ℕ) (P R : ℝ) (n : ℕ) :
    mixedRepresentationIntegral k u v P R n =
      (mixedRepresentationCount k u v P R n : ℂ) := by
  unfold mixedRepresentationIntegral
  simp_rw [mixedWeyl_product_expansion]
  have h := interval_integral_finite_frequency_coefficient
    (mixedTuples (ordinaryNumbers P) u (smoothNumbers P R) v)
    (fun f => ((mixedPowerSum k f : ℕ) : ℤ)) (n : ℤ)
  simpa only [Nat.cast_inj, mixedRepresentationCount, mixedRepresentationSet] using h

theorem mixedIntegral_re_eq_count (k u v : ℕ) (P R : ℝ) (n : ℕ) :
    (mixedRepresentationIntegral k u v P R n).re =
      (mixedRepresentationCount k u v P R n : ℝ) := by
  rw [mixedIntegral_eq_count]
  simp

/-- All range and smoothness restrictions are explicit in membership. -/
theorem mem_mixedRepresentationSet {k u v n : ℕ} {P R : ℝ}
    {f : (Fin u → ℕ) × (Fin v → ℕ)} :
    f ∈ mixedRepresentationSet k u v P R n ↔
      (∀ i, f.1 i ∈ ordinaryNumbers P) ∧
      (∀ j, f.2 j ∈ smoothNumbers P R) ∧ mixedPowerSum k f = n := by
  simp only [mixedRepresentationSet, Finset.mem_filter, mixedTuples,
    Finset.mem_product, finiteTuples, Fintype.mem_piFinset, and_assoc]

/-- Concatenating a counted mixed tuple gives the actual positive-summand
representation predicate. Neither ordinary nor smooth variables can be zero. -/
theorem representable_of_mixed_count_pos {k u v n : ℕ} {P R : ℝ}
    (h : 0 < mixedRepresentationCount k u v P R n) :
    RepresentableByAtMost k (u+v) n := by
  obtain ⟨f,hf⟩ := Finset.card_pos.mp h
  rcases mem_mixedRepresentationSet.mp hf with ⟨hordinary,hsmooth,hsum⟩
  refine ⟨u+v,le_rfl,Fin.append f.1 f.2,?_,?_⟩
  · intro i
    refine Fin.addCases (m := u) (n := v) ?_ ?_ i
    · intro j
      have hpos : 1 ≤ f.1 j := (Finset.mem_Icc.mp (hordinary j)).1
      simpa only [Fin.append_left] using (Nat.zero_lt_one.trans_le hpos)
    · intro j
      have hpos : 1 ≤ f.2 j := (mem_smoothNumbers.mp (hsmooth j)).1.1
      simpa only [Fin.append_right] using (Nat.zero_lt_one.trans_le hpos)
  · rw [Fin.sum_univ_add]
    simpa only [Fin.append_left,Fin.append_right,mixedPowerSum] using hsum

/-- Positivity of the real part of the mixed integral forces a genuine representation. -/
theorem representable_of_mixed_integral_pos {k u v n : ℕ} {P R : ℝ}
    (h : 0 < (mixedRepresentationIntegral k u v P R n).re) :
    RepresentableByAtMost k (u+v) n := by
  rw [mixedIntegral_re_eq_count] at h
  apply representable_of_mixed_count_pos
  exact_mod_cast h

/-- The cutoffs may be chosen as functions of n, for example the usual
P approximately n^(1/k). Only eventual positivity remains an analytic premise. -/
theorem waringBound_of_eventually_mixed_integral_pos {k u v : ℕ}
    (P R : ℕ → ℝ)
    (h : ∃ N : ℕ, ∀ n ≥ N, 0 < (mixedRepresentationIntegral k u v (P n) (R n) n).re) :
    WaringBound k (u+v) := by
  obtain ⟨N,hN⟩ := h
  exact ⟨N,fun n hn => representable_of_mixed_integral_pos (hN n hn)⟩

theorem waring8_of_eventually_mixed_integral_pos (P R : ℕ → ℝ)
    (h : ∃ N : ℕ, ∀ n ≥ N, 0 < (mixedRepresentationIntegral 8 8 30 (P n) (R n) n).re) :
    WaringBound 8 38 := by
  exact waringBound_of_eventually_mixed_integral_pos P R h

theorem waring9_of_eventually_mixed_integral_pos (P R : ℕ → ℝ)
    (h : ∃ N : ℕ, ∀ n ≥ N, 0 < (mixedRepresentationIntegral 9 11 35 (P n) (R n) n).re) :
    WaringBound 9 46 := by
  exact waringBound_of_eventually_mixed_integral_pos P R h

#print axioms mixedIntegral_eq_count
#print axioms representable_of_mixed_count_pos
#print axioms waring8_of_eventually_mixed_integral_pos
#print axioms waring9_of_eventually_mixed_integral_pos
end Waring
