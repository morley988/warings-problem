import Waring.QuadraticModulation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Ordinary differencing before separating coefficient parameters

The parameter tuple is a single finite-family index. Cauchy's inequality is
applied over that existing tuple. Positive ordinary shifts are appended to
it, and the resulting sum is retained as one complex quantity until after
the next difference. No independent copy of the coefficient tuple occurs.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Waring.UnseparatedDifferencing
open QuadraticModulation

def positivePairs (S : Finset ℤ) : Finset (ℤ × ℤ) :=
  (S ×ˢ S).filter (fun p => p.2 < p.1)

def positiveDifference (S : Finset ℤ) (f : ℤ → ℂ) (N : ℕ) : ℂ :=
  ∑ u ∈ Finset.Icc (1 : ℤ) (N : ℤ), ∑ z ∈ overlap S u, f (z+u)*conj (f z)

private theorem diagonal_pair_sum (S : Finset ℤ) (f : ℤ → ℂ) :
    (∑ p ∈ (S ×ˢ S).filter (fun p => p.1=p.2), f p.1*conj (f p.2)) =
      ∑ z ∈ S, ((‖f z‖^2 : ℝ) : ℂ) := by
  apply Finset.sum_bij (fun p _ => p.1)
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq heq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    exact Prod.ext heq (by omega)
  · intro z hz
    exact ⟨(z,z), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz,hz⟩,rfl⟩,rfl⟩
  · intro p hp
    rw [(Finset.mem_filter.mp hp).2, Complex.mul_conj']
    simp only [Complex.ofReal_pow]

private theorem negative_pair_sum (S : Finset ℤ) (f : ℤ → ℂ) :
    (∑ p ∈ (S ×ˢ S).filter (fun p => p.1<p.2), f p.1*conj (f p.2)) =
      conj (∑ p ∈ positivePairs S, f p.1*conj (f p.2)) := by
  rw [map_sum]
  apply Finset.sum_bij (fun p _ => (p.2,p.1))
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hlt⟩
    rcases Finset.mem_product.mp hp with ⟨h1,h2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2,h1⟩,hlt⟩
  · intro p _ q _ heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hq,hlt⟩
    rcases Finset.mem_product.mp hq with ⟨h1,h2⟩
    exact ⟨(q.2,q.1),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2,h1⟩,hlt⟩,rfl⟩
  · intro p _
    simp only [map_mul, Complex.conj_conj]
    ring

/-- Exact positive/negative decomposition. The positive correlation is
retained as a complex sum, rather than replaced by a sum of its magnitudes. -/
theorem norm_sq_positive_pairs (S : Finset ℤ) (f : ℤ → ℂ) :
    ‖∑ z ∈ S, f z‖^2 = (∑ z ∈ S, ‖f z‖^2)+
      2*(∑ p ∈ positivePairs S, f p.1*conj (f p.2)).re := by
  have hsplit : (∑ p ∈ S ×ˢ S, f p.1*conj (f p.2)) =
      (∑ p ∈ (S ×ˢ S).filter (fun p => p.1=p.2), f p.1*conj (f p.2))+
      (∑ p ∈ positivePairs S, f p.1*conj (f p.2))+
      (∑ p ∈ (S ×ˢ S).filter (fun p => p.1<p.2), f p.1*conj (f p.2)) := by
    simp only [positivePairs, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  rw [diagonal_pair_sum, negative_pair_sum] at hsplit
  have h := congrArg Complex.re ((norm_sq_eq_pair_sum S f).trans hsplit)
  simpa only [Complex.ofReal_re, Complex.add_re, Complex.re_sum, Complex.conj_re,
    ← two_mul, add_assoc] using h

/-- Positive pairs are precisely the original-domain overlaps at positive
shifts. The finite width condition permits a fixed common shift range. -/
theorem positive_pairs_eq_differences (S : Finset ℤ) (f : ℤ → ℂ) (N : ℕ)
    (hwidth : ∀ z ∈ S, ∀ w ∈ S, z-w ≤ (N : ℤ)) :
    (∑ p ∈ positivePairs S, f p.1*conj (f p.2)) = positiveDifference S f N := by
  have hmap : ∀ p ∈ positivePairs S, p.1-p.2 ∈ Finset.Icc (1 : ℤ) (N : ℤ) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hlt⟩
    rcases Finset.mem_product.mp hp with ⟨h1,h2⟩
    exact Finset.mem_Icc.mpr ⟨by omega,hwidth p.1 h1 p.2 h2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  unfold positiveDifference
  apply Finset.sum_congr rfl
  intro u hu
  have hu1 := (Finset.mem_Icc.mp hu).1
  have hfilter : (positivePairs S).filter (fun p => p.1-p.2=u) =
      (S ×ˢ S).filter (fun p => p.1-p.2=u) := by
    ext p
    simp only [positivePairs, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1.1,h.2⟩
    · intro h
      have heq := h.2
      exact ⟨⟨h.1,by omega⟩,h.2⟩
  rw [hfilter]
  exact difference_fiber_sum S f u

def familySum {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ) (f : ι → ℤ → ℂ) : ℂ :=
  ∑ b ∈ B, ∑ z ∈ domain b, f b z

def differenceParameters {ι : Type*} (B : Finset ι) (N : ℕ) : Finset (ι × ℤ) :=
  B ×ˢ Finset.Icc (1 : ℤ) (N : ℤ)

def differenceDomain {ι : Type*} (domain : ι → Finset ℤ) (bu : ι × ℤ) : Finset ℤ :=
  overlap (domain bu.1) bu.2

def differenceFunction {ι : Type*} (f : ι → ℤ → ℂ) (bu : ι × ℤ) (z : ℤ) : ℂ :=
  f bu.1 (z+bu.2)*conj (f bu.1 z)

/-- One original parameter and one ordinary shift, retained together. -/
def firstDifference {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ)
    (f : ι → ℤ → ℂ) (N : ℕ) : ℂ :=
  familySum (differenceParameters B N) (differenceDomain domain) (differenceFunction f)

/-- One original parameter and two ordinary shifts. No new copy of the
original parameter family is introduced by the second difference. -/
def secondDifference {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ)
    (f : ι → ℤ → ℂ) (N : ℕ) : ℂ :=
  firstDifference (differenceParameters B N) (differenceDomain domain) (differenceFunction f) N

theorem firstDifference_eq {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ)
    (f : ι → ℤ → ℂ) (N : ℕ) :
    firstDifference B domain f N = ∑ b ∈ B, positiveDifference (domain b) (f b) N := by
  simp only [firstDifference, familySum, differenceParameters, Finset.sum_product,
    differenceDomain, differenceFunction, positiveDifference]

/-- Finite Cauchy over exactly the existing parameter family. -/
theorem family_cauchy {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ)
    (f : ι → ℤ → ℂ) :
    ‖familySum B domain f‖^2 ≤ (B.card : ℝ)*∑ b ∈ B, ‖∑ z ∈ domain b, f b z‖^2 := by
  have hnorm := norm_sum_le B (fun b => ∑ z ∈ domain b, f b z)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1 : ℝ))
    (fun b => ‖∑ z ∈ domain b, f b z‖)
  apply hs.trans
  simpa using hc

/-- The first unseparated ordinary difference, with explicit constant two. -/
theorem first_unseparated_bound {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ)
    (f : ι → ℤ → ℂ) (N : ℕ)
    (hcard : ∀ b ∈ B, (domain b).card ≤ N)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ))
    (hnorm : ∀ b ∈ B, ∀ z, ‖f b z‖ ≤ 1) :
    ‖familySum B domain f‖^2 ≤
      (N : ℝ)*(B.card : ℝ)^2+2*(B.card : ℝ)*‖firstDifference B domain f N‖ := by
  have hpoint (b : ι) (hb : b ∈ B) :
      ‖∑ z ∈ domain b, f b z‖^2 ≤ (N : ℝ)+2*(positiveDifference (domain b) (f b) N).re := by
    rw [norm_sq_positive_pairs, positive_pairs_eq_differences _ _ _ (hwidth b hb)]
    apply add_le_add_right
    calc
      (∑ z ∈ domain b, ‖f b z‖^2) ≤ ∑ _z ∈ domain b, (1 : ℝ) :=
        Finset.sum_le_sum (fun z _ => by nlinarith [hnorm b hb z, norm_nonneg (f b z)])
      _ = (domain b).card := by simp
      _ ≤ N := by exact_mod_cast hcard b hb
  have hsum := Finset.sum_le_sum hpoint
  have hbound : (∑ b ∈ B, ‖∑ z ∈ domain b, f b z‖^2) ≤
      (B.card : ℝ)*N+2*(firstDifference B domain f N).re := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Complex.re_sum, ← firstDifference_eq] using hsum
  have hre : (firstDifference B domain f N).re ≤ ‖firstDifference B domain f N‖ :=
    Complex.re_le_norm _
  have hmul := mul_le_mul_of_nonneg_left hbound (show (0 : ℝ) ≤ B.card by positivity)
  have hmul2 := mul_le_mul_of_nonneg_left hre (show 0 ≤ 2*(B.card : ℝ) by positivity)
  have hc := family_cauchy B domain f
  nlinarith

theorem differenceParameters_card {ι : Type*} (B : Finset ι) (N : ℕ) :
    (differenceParameters B N).card = B.card*N := by
  simp [differenceParameters, Finset.card_product, Int.card_Icc]

theorem differenceDomain_card_le {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ)
    (N : ℕ) (hcard : ∀ b ∈ B, (domain b).card ≤ N) :
    ∀ bu ∈ differenceParameters B N, (differenceDomain domain bu).card ≤ N := by
  intro bu hbu
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (hcard bu.1 (Finset.mem_product.mp hbu).1)

theorem differenceDomain_width {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ)
    (N : ℕ)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ)) :
    ∀ bu ∈ differenceParameters B N, ∀ z ∈ differenceDomain domain bu,
      ∀ w ∈ differenceDomain domain bu, z-w ≤ (N : ℤ) := by
  intro bu hbu z hz w hw
  exact hwidth bu.1 (Finset.mem_product.mp hbu).1 z (Finset.mem_filter.mp hz).1
    w (Finset.mem_filter.mp hw).1

theorem differenceFunction_norm_le {ι : Type*} (B : Finset ι) (f : ι → ℤ → ℂ) (N : ℕ)
    (hnorm : ∀ b ∈ B, ∀ z, ‖f b z‖ ≤ 1) :
    ∀ bu ∈ differenceParameters B N, ∀ z, ‖differenceFunction f bu z‖ ≤ 1 := by
  intro bu hbu z
  have hb := (Finset.mem_product.mp hbu).1
  rw [differenceFunction, norm_mul, Complex.norm_conj]
  have h1 := hnorm bu.1 hb (z+bu.2)
  have h2 := hnorm bu.1 hb z
  nlinarith [norm_nonneg (f bu.1 (z+bu.2)), norm_nonneg (f bu.1 z)]

/-- The second application still has precisely one original parameter tuple;
its only extra index is the first ordinary shift. -/
theorem firstDifference_sq_bound {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ)
    (f : ι → ℤ → ℂ) (N : ℕ)
    (hcard : ∀ b ∈ B, (domain b).card ≤ N)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ))
    (hnorm : ∀ b ∈ B, ∀ z, ‖f b z‖ ≤ 1) :
    ‖firstDifference B domain f N‖^2 ≤
      (N : ℝ)^3*(B.card : ℝ)^2+
        2*(N : ℝ)*(B.card : ℝ)*‖secondDifference B domain f N‖ := by
  have h := first_unseparated_bound (differenceParameters B N) (differenceDomain domain)
    (differenceFunction f) N (differenceDomain_card_le B domain N hcard)
    (differenceDomain_width B domain N hwidth) (differenceFunction_norm_le B f N hnorm)
  change ‖firstDifference B domain f N‖^2 ≤
    (N : ℝ)*((differenceParameters B N).card : ℝ)^2+
      2*((differenceParameters B N).card : ℝ)*‖secondDifference B domain f N‖ at h
  rw [differenceParameters_card, Nat.cast_mul] at h
  convert h using 1
  ring

private theorem two_step_scalar {X Y Z N B : ℝ} (hN : 1 ≤ N) (_hB : 0 ≤ B)
    (hfirst : X^2 ≤ N*B^2+2*B*Y) (hsecond : Y^2 ≤ N^3*B^2+2*N*B*Z) :
    X^4 ≤ 16*(N^3*B^4+N*B^3*Z) := by
  have hs := pow_le_pow_left₀ (sq_nonneg X) hfirst 2
  have hsplit : X^4 ≤ 2*N^2*B^4+8*B^2*Y^2 := by
    nlinarith [sq_nonneg (N*B^2-2*B*Y)]
  have hN23 : N^2 ≤ N^3 := by
    have h := mul_nonneg (sq_nonneg N) (sub_nonneg.mpr hN)
    nlinarith
  have hNB := mul_le_mul_of_nonneg_right hN23 (show 0 ≤ B^4 by positivity)
  calc
    X^4 ≤ 2*N^2*B^4+8*B^2*Y^2 := hsplit
    _ ≤ 2*N^2*B^4+8*B^2*(N^3*B^2+2*N*B*Z) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hsecond (by positivity)) _
    _ = 2*N^2*B^4+8*N^3*B^4+16*N*B^3*Z := by ring
    _ ≤ 16*(N^3*B^4+N*B^3*Z) := by
      have hnonneg : 0 ≤ N^3*B^4 := by positivity
      nlinarith

/-- Two ordinary differences, with an explicit fixed constant and no
premature separation of the coefficient tuple. -/
theorem second_unseparated_bound {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ)
    (f : ι → ℤ → ℂ) (N : ℕ) (hN : 0 < N)
    (hcard : ∀ b ∈ B, (domain b).card ≤ N)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ))
    (hnorm : ∀ b ∈ B, ∀ z, ‖f b z‖ ≤ 1) :
    ‖familySum B domain f‖^4 ≤ 16*((N : ℝ)^3*(B.card : ℝ)^4+
      (N : ℝ)*(B.card : ℝ)^3*‖secondDifference B domain f N‖) := by
  exact two_step_scalar (by exact_mod_cast hN) (by positivity)
    (first_unseparated_bound B domain f N hcard hwidth hnorm)
    (firstDifference_sq_bound B domain f N hcard hwidth hnorm)

theorem differenceFunction_phase {ι : Type*} (phase : ι → ℤ → ℝ) (bu : ι × ℤ) (z : ℤ) :
    differenceFunction (fun b x => e (phase b x)) bu z =
      e (phase bu.1 (z+bu.2)-phase bu.1 z) := by
  exact e_mul_conj _ _

theorem secondDifferenceFunction_phase {ι : Type*} (phase : ι → ℤ → ℝ)
    (b : ι) (u v z : ℤ) :
    differenceFunction (differenceFunction (fun b x => e (phase b x))) ((b,u),v) z =
      e (phase b (z+v+u)-phase b (z+v)-phase b (z+u)+phase b z) := by
  change (differenceFunction (fun b x => e (phase b x)) (b,u) (z+v))*
    conj (differenceFunction (fun b x => e (phase b x)) (b,u) z) = _
  rw [differenceFunction_phase, differenceFunction_phase, e_mul_conj]
  congr 1
  ring

/-- Exponential phases satisfy the magnitude premise identically. -/
theorem first_unseparated_phase_bound {ι : Type*} (B : Finset ι)
    (domain : ι → Finset ℤ) (phase : ι → ℤ → ℝ) (N : ℕ)
    (hcard : ∀ b ∈ B, (domain b).card ≤ N)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ)) :
    ‖familySum B domain (fun b z => e (phase b z))‖^2 ≤
      (N : ℝ)*(B.card : ℝ)^2+
        2*(B.card : ℝ)*‖firstDifference B domain (fun b z => e (phase b z)) N‖ :=
  first_unseparated_bound B domain _ N hcard hwidth (by intros; simp only [norm_e, le_refl])

/-- The exact source case of two differences of a family of exponential sums. -/
theorem second_unseparated_phase_bound {ι : Type*} (B : Finset ι)
    (domain : ι → Finset ℤ) (phase : ι → ℤ → ℝ) (N : ℕ) (hN : 0 < N)
    (hcard : ∀ b ∈ B, (domain b).card ≤ N)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ)) :
    ‖familySum B domain (fun b z => e (phase b z))‖^4 ≤
      16*((N : ℝ)^3*(B.card : ℝ)^4+(N : ℝ)*(B.card : ℝ)^3*
        ‖secondDifference B domain (fun b z => e (phase b z)) N‖) :=
  second_unseparated_bound B domain _ N hN hcard hwidth (by intros; simp only [norm_e, le_refl])

/-- For positive shifts of a Cartesian integer interval, only its upper
endpoint changes. No coefficient parameter enters the new endpoint. -/
theorem differenceDomain_interval {ι : Type*} (a b u : ℤ) (i : ι) (hu : 0 ≤ u) :
    differenceDomain (fun _ : ι => Finset.Icc a b) (i,u) = Finset.Icc a (b-u) := by
  rw [differenceDomain, overlap_Icc]
  rw [max_eq_left (by omega : a-u ≤ a), min_eq_right (by omega : b-u ≤ b)]

/-- After two positive ordinary shifts, the interval depends on their sum
and remains independent of the original coefficient tuple. -/
theorem secondDifferenceDomain_interval {ι : Type*} (a b u v : ℤ) (i : ι)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    differenceDomain (differenceDomain (fun _ : ι => Finset.Icc a b)) ((i,u),v) =
      Finset.Icc a (b-u-v) := by
  change overlap (differenceDomain (fun _ : ι => Finset.Icc a b) (i,u)) v = _
  rw [differenceDomain_interval a b u i hu, overlap_Icc]
  rw [max_eq_left (by omega : a-v ≤ a), min_eq_right (by omega : b-u-v ≤ b-u)]

/-- The Cartesian interval instance used before separating coefficient sums. -/
theorem first_interval_family_bound {ι : Type*} (B : Finset ι) (phase : ι → ℤ → ℝ)
    (a b : ℤ) (N : ℕ) (hlength : b+1-a ≤ (N : ℤ)) :
    ‖familySum B (fun _ => Finset.Icc a b) (fun i z => e (phase i z))‖^2 ≤
      (N : ℝ)*(B.card : ℝ)^2+2*(B.card : ℝ)*
        ‖firstDifference B (fun _ => Finset.Icc a b) (fun i z => e (phase i z)) N‖ := by
  apply first_unseparated_phase_bound
  · intro i hi
    rw [Int.card_Icc]
    omega
  · intro i hi z hz w hw
    rcases Finset.mem_Icc.mp hz with ⟨hza,hzb⟩
    rcases Finset.mem_Icc.mp hw with ⟨hwa,hwb⟩
    omega

/-- Two-difference Cartesian instance with one unchanged coefficient tuple. -/
theorem second_interval_family_bound {ι : Type*} (B : Finset ι) (phase : ι → ℤ → ℝ)
    (a b : ℤ) (N : ℕ) (hN : 0 < N) (hlength : b+1-a ≤ (N : ℤ)) :
    ‖familySum B (fun _ => Finset.Icc a b) (fun i z => e (phase i z))‖^4 ≤
      16*((N : ℝ)^3*(B.card : ℝ)^4+(N : ℝ)*(B.card : ℝ)^3*
        ‖secondDifference B (fun _ => Finset.Icc a b) (fun i z => e (phase i z)) N‖) := by
  apply second_unseparated_phase_bound B _ _ N hN
  · intro i hi
    rw [Int.card_Icc]
    omega
  · intro i hi z hz w hw
    rcases Finset.mem_Icc.mp hz with ⟨hza,hzb⟩
    rcases Finset.mem_Icc.mp hw with ⟨hwa,hwb⟩
    omega

/-- Real upper bounds for the length and parameter count may replace their
integer values after the unseparated argument is complete. -/
theorem first_unseparated_real_bound {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ)
    (f : ι → ℤ → ℂ) (N : ℕ) (P C : ℝ)
    (hNP : (N : ℝ) ≤ P) (hBC : (B.card : ℝ) ≤ C)
    (hcard : ∀ b ∈ B, (domain b).card ≤ N)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ))
    (hnorm : ∀ b ∈ B, ∀ z, ‖f b z‖ ≤ 1) :
    ‖familySum B domain f‖^2 ≤ P*C^2+2*C*‖firstDifference B domain f N‖ := by
  have hP : 0 ≤ P := (show (0 : ℝ) ≤ N by positivity).trans hNP
  have hB : (0 : ℝ) ≤ B.card := by positivity
  have hC : 0 ≤ C := hB.trans hBC
  have hdiag := mul_le_mul hNP (pow_le_pow_left₀ hB hBC 2) (sq_nonneg _) hP
  have hlast := mul_le_mul_of_nonneg_right hBC (norm_nonneg (firstDifference B domain f N))
  have h := first_unseparated_bound B domain f N hcard hwidth hnorm
  nlinarith

/-- The real-parameter form of the two-difference source inequality. -/
theorem second_unseparated_real_bound {ι : Type*} (B : Finset ι) (domain : ι → Finset ℤ)
    (f : ι → ℤ → ℂ) (N : ℕ) (P C : ℝ) (hN : 0 < N)
    (hNP : (N : ℝ) ≤ P) (hBC : (B.card : ℝ) ≤ C)
    (hcard : ∀ b ∈ B, (domain b).card ≤ N)
    (hwidth : ∀ b ∈ B, ∀ z ∈ domain b, ∀ w ∈ domain b, z-w ≤ (N : ℤ))
    (hnorm : ∀ b ∈ B, ∀ z, ‖f b z‖ ≤ 1) :
    ‖familySum B domain f‖^4 ≤
      16*(P^3*C^4+P*C^3*‖secondDifference B domain f N‖) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hP : 0 ≤ P := hN0.trans hNP
  have hB : (0 : ℝ) ≤ B.card := by positivity
  have hdiag := mul_le_mul (pow_le_pow_left₀ hN0 hNP 3)
    (pow_le_pow_left₀ hB hBC 4) (by positivity : (0 : ℝ) ≤ (B.card : ℝ)^4)
    (pow_nonneg hP 3)
  have hpre := mul_le_mul hNP (pow_le_pow_left₀ hB hBC 3)
    (pow_nonneg hB 3) hP
  have hlast := mul_le_mul_of_nonneg_right hpre (norm_nonneg (secondDifference B domain f N))
  have h := second_unseparated_bound B domain f N hN hcard hwidth hnorm
  nlinarith

#print axioms first_unseparated_bound
#print axioms second_unseparated_bound
#print axioms second_unseparated_phase_bound
#print axioms second_interval_family_bound
#print axioms second_unseparated_real_bound

end Waring.UnseparatedDifferencing
