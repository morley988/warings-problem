import Waring.CartesianProductSampling
import Waring.NormalizedQuadraticSecond
import Waring.NormalizedQuadraticFourth
import Waring.NormalizedCoefficient

/-!
# Actual Cartesian resource moments and the proved sampled operators

These inequalities group literal positive tuples, with the exact finite
average normalization. The optional padded cutoff has the explicit ratio
Cpad. Quadratic sampling uses one common t. Coefficient sampling fixes its
own h coordinate and uses the positive sampled range, hence sigma=1.
-/

noncomputable section
open scoped BigOperators
namespace Waring.CartesianResourceMoments
open CartesianProductSampling ProductMultiplicity FiniteResourceHolder
open CoefficientFactorization CoefficientPower

def quadraticBoxMoment {r : ℕ} (bounds : Fin r → ℕ) (S : Finset ℤ)
    (cap α t : ℝ) (c q : ℕ) : ℝ :=
  average (fun x : positiveBox bounds =>
    (‖quadraticSum S ((c:ℝ)*((tupleProduct x.val:ℝ)*α)) t‖/cap)^q)

theorem quadratic_second_sample_identity (S : Finset ℤ) (P α t : ℝ) (c J : ℕ) :
    (∑ n ∈ Finset.Icc 1 J, (‖quadraticSum S ((c:ℝ)*((n:ℝ)*α)) t‖/P)^2)/(J:ℝ) =
      NormalizedQuadratic.normalizedSecond S P α t c J := by
  have hraw : (∑ n ∈ Finset.Icc 1 J, ‖quadraticSum S ((c:ℝ)*((n:ℝ)*α)) t‖^2) =
      SampledQuadraticSecond.sampledMoment S ((c:ℝ)*α) t J := by
    rw [sum_Icc_one_eq_range]
    unfold SampledQuadraticSecond.sampledMoment
    apply Finset.sum_congr rfl
    intro n hn
    have hs : quadraticSum S ((c:ℝ)*(((n+1:ℕ):ℝ)*α)) t =
        ∑ z ∈ S, QuadraticModulation.e (((c:ℝ)*α)*((n:ℝ)+1)*(z:ℝ)^2+t*z) := by
      unfold quadraticSum
      apply Finset.sum_congr rfl
      intro z hz
      congr 1
      push_cast
      ring
    rw [hs]
  simp_rw [div_pow]
  rw [← Finset.sum_div, hraw]
  unfold NormalizedQuadratic.normalizedSecond
  ring

theorem quadratic_fourth_sample_identity (a b : ℤ) (P α t : ℝ) (c J : ℕ) :
    (∑ n ∈ Finset.Icc 1 J, (‖quadraticSum (Finset.Icc a b) ((c:ℝ)*((n:ℝ)*α)) t‖/P)^4)/(J:ℝ) =
      NormalizedQuadratic.normalizedFourth (Finset.Icc 1 J) (fun _ => a) (fun _ => b)
        (fun _ => t) c P J α := by
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  unfold NormalizedQuadratic.normalizedFourth quadraticSum
  ring

/-- Actual tuple z2 moments transfer to the proved normalized second moment
with the explicit padded-volume factor and a genuine P^epsilon loss. -/
theorem quadratic_second_box_to_sample (r : ℕ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ P : ℝ, 1 ≤ P → ∀ bounds : Fin r → ℕ,
      (∀ i, 0 < bounds i) → ∀ J : ℕ, tupleProduct bounds ≤ J → (J:ℝ) ≤ P^B →
      ∀ Cpad : ℝ, (J:ℝ) ≤ Cpad*(tupleProduct bounds:ℝ) →
      ∀ (S : Finset ℤ) (α t : ℝ) (c : ℕ),
      quadraticBoxMoment bounds S P α t c 2 ≤
        D*Cpad*P^ε*NormalizedQuadratic.normalizedSecond S P α t c J := by
  obtain ⟨D,hD,hgroup⟩ := padded_product_average r hB hε
  refine ⟨D,hD,?_⟩
  intro P hP bounds hb J hVJ hJP Cpad hpad S α t c
  have HH := hgroup P hP bounds hb J hVJ hJP Cpad hpad
    (fun n => (‖quadraticSum S ((c:ℝ)*((n:ℝ)*α)) t‖/P)^2)
    (fun _ _ => sq_nonneg _)
  rw [quadratic_second_sample_identity] at HH
  unfold quadraticBoxMoment
  rw [average_positiveBox bounds (fun x => (‖quadraticSum S ((c:ℝ)*((tupleProduct x:ℝ)*α)) t‖/P)^2)]
  exact HH

/-- Actual tuple z4 moments transfer to the proved normalized fourth moment.
The basic and refined resource branches may then both be applied. -/
theorem quadratic_fourth_box_to_sample (r : ℕ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ P : ℝ, 1 ≤ P → ∀ bounds : Fin r → ℕ,
      (∀ i, 0 < bounds i) → ∀ J : ℕ, tupleProduct bounds ≤ J → (J:ℝ) ≤ P^B →
      ∀ Cpad : ℝ, (J:ℝ) ≤ Cpad*(tupleProduct bounds:ℝ) →
      ∀ (a b : ℤ) (α t : ℝ) (c : ℕ),
      quadraticBoxMoment bounds (Finset.Icc a b) P α t c 4 ≤
        D*Cpad*P^ε*NormalizedQuadratic.normalizedFourth (Finset.Icc 1 J)
          (fun _ => a) (fun _ => b) (fun _ => t) c P J α := by
  obtain ⟨D,hD,hgroup⟩ := padded_product_average r hB hε
  refine ⟨D,hD,?_⟩
  intro P hP bounds hb J hVJ hJP Cpad hpad a b α t c
  have HH := hgroup P hP bounds hb J hVJ hJP Cpad hpad
    (fun n => (‖quadraticSum (Finset.Icc a b) ((c:ℝ)*((n:ℝ)*α)) t‖/P)^4)
    (fun _ _ => pow_nonneg (div_nonneg (norm_nonneg _) (zero_le_one.trans hP)) _)
  rw [quadratic_fourth_sample_identity] at HH
  unfold quadraticBoxMoment
  rw [average_positiveBox bounds (fun x =>
    (‖quadraticSum (Finset.Icc a b) ((c:ℝ)*((tupleProduct x:ℝ)*α)) t‖/P)^4)]
  exact HH

def coefficientBoxMoment {r : ℕ} (bounds : Fin (r+1) → ℕ)
    (C : Finset ℕ) (degree power : ℕ) (cap α : ℝ) : ℝ :=
  average (fun x : positiveBox bounds =>
    (‖coefficientWeyl C degree (α*(tupleProduct x.val:ℝ)*(x.val 0:ℝ)^2)‖/cap)^(2*power))

theorem coefficient_box_argument {r : ℕ} (x : Fin (r+1) → ℕ) (α : ℝ) :
    α*(tupleProduct x:ℝ)*(x 0:ℝ)^2 =
      α*(x 0:ℝ)^3*(tupleProduct (fun i => x i.succ):ℝ) := by
  simp only [tupleProduct, Fin.prod_univ_succ, Nat.cast_mul]
  ring

theorem coefficientBoxMoment_eq_nested {r : ℕ} (bounds : Fin (r+1) → ℕ)
    (C : Finset ℕ) (degree power : ℕ) (cap α : ℝ) :
    coefficientBoxMoment bounds C degree power cap α =
      (∑ h ∈ Finset.Icc 1 (bounds 0),
        ∑ x ∈ positiveBox (fun i => bounds i.succ),
          (‖coefficientWeyl C degree (α*(h:ℝ)^3*(tupleProduct x:ℝ))‖/cap)^(2*power))/
        ((bounds 0:ℝ)*(tupleProduct (fun i => bounds i.succ):ℝ)) := by
  unfold coefficientBoxMoment
  rw [average_positiveBox bounds (fun x =>
    (‖coefficientWeyl C degree (α*(tupleProduct x:ℝ)*(x 0:ℝ)^2)‖/cap)^(2*power))]
  simp_rw [coefficient_box_argument]
  exact fullbox_distinguished_average bounds
    (fun h z => (‖coefficientWeyl C degree (α*(h:ℝ)^3*(z:ℝ))‖/cap)^(2*power))

theorem coefficient_sample_normalized_identity (C : Finset ℕ) (degree power H J : ℕ)
    (P phi α : ℝ) (hP : 0 < P) :
    (∑ h ∈ Finset.Icc 1 H, ∑ z ∈ Finset.Icc 1 J,
      (‖coefficientWeyl C degree (α*(h:ℝ)^3*(z:ℝ))‖/P^phi)^(2*power))/((H:ℝ)*J) =
      NormalizedCoefficient.normalizedSampledCoefficient C degree power P phi H J α (fun _ => 1) := by
  have hcap : (P^phi)^(2*power) = P^((2*power:ℕ)*phi) := by
    rw [← Real.rpow_mul_natCast hP.le]
    congr 1
    ring
  simp_rw [div_pow, hcap]
  simp_rw [← Finset.sum_div]
  have hsum : (∑ h ∈ Finset.Icc 1 H, ∑ z ∈ Finset.Icc 1 J,
      ‖coefficientWeyl C degree (α*(h:ℝ)^3*(z:ℝ))‖^(2*power)) =
      ∑ h ∈ Finset.Icc 1 H, ∑ j ∈ Finset.range J,
        ‖coefficientWeyl C degree (α*(h:ℝ)^3*((j:ℝ)+1))‖^(2*power) := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [sum_Icc_one_eq_range]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hsum]
  unfold NormalizedCoefficient.normalizedSampledCoefficient
  ring

/-- The literal Gamma*h_i^2 coefficient resource on the full tuple box
reduces to the proved cubic sampled coefficient moment with sigma=1. The
positive padded cutoff J and its volume ratio remain explicit. -/
theorem coefficient_box_to_sample (r : ℕ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ P : ℝ, 1 ≤ P → ∀ bounds : Fin (r+1) → ℕ,
      (∀ i, 0 < bounds i) → ∀ J : ℕ,
      tupleProduct (fun i => bounds i.succ) ≤ J → (J:ℝ) ≤ P^B →
      ∀ Cpad : ℝ, (J:ℝ) ≤ Cpad*(tupleProduct (fun i => bounds i.succ):ℝ) →
      ∀ (C : Finset ℕ) (degree power : ℕ) (phi α : ℝ),
      coefficientBoxMoment bounds C degree power (P^phi) α ≤
        D*Cpad*P^ε*NormalizedCoefficient.normalizedSampledCoefficient C degree power
          P phi (bounds 0) J α (fun _ => 1) := by
  obtain ⟨D,hD,hgroup⟩ := padded_distinguished_average r hB hε
  refine ⟨D,hD,?_⟩
  intro P hP bounds hb J hVJ hJP Cpad hpad C degree power phi α
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have HH := hgroup P hP (bounds 0) (hb 0) (fun i => bounds i.succ) (fun i => hb i.succ)
    J hVJ hJP Cpad hpad
    (fun h z => (‖coefficientWeyl C degree (α*(h:ℝ)^3*(z:ℝ))‖/P^phi)^(2*power))
    (fun _ _ _ _ => pow_nonneg (div_nonneg (norm_nonneg _) (Real.rpow_nonneg hPp.le _)) _)
  rw [coefficient_sample_normalized_identity C degree power (bounds 0) J P phi α hPp] at HH
  rw [coefficientBoxMoment_eq_nested]
  exact HH

def coefficientBoxMomentAt {r : ℕ} (bounds : Fin (r+1) → ℕ) (i : Fin (r+1))
    (C : Finset ℕ) (degree power : ℕ) (cap α : ℝ) : ℝ :=
  average (fun x : positiveBox bounds =>
    (‖coefficientWeyl C degree (α*(tupleProduct x.val:ℝ)*(x.val i:ℝ)^2)‖/cap)^(2*power))

/-- Any distinguished coordinate is moved to the head by an exact finite
permutation. This preserves the full original tuple volume. -/
theorem coefficientBoxMomentAt_reindex {r : ℕ} (bounds : Fin (r+1) → ℕ)
    (i : Fin (r+1)) (e : Fin (r+1) ≃ Fin (r+1)) (he : e 0=i)
    (C : Finset ℕ) (degree power : ℕ) (cap α : ℝ) :
    coefficientBoxMomentAt bounds i C degree power cap α =
      coefficientBoxMoment (fun l => bounds (e l)) C degree power cap α := by
  unfold coefficientBoxMomentAt coefficientBoxMoment
  rw [average_positiveBox bounds (fun x =>
    (‖coefficientWeyl C degree (α*(tupleProduct x:ℝ)*(x i:ℝ)^2)‖/cap)^(2*power)),
    average_positiveBox (fun l => bounds (e l)) (fun x =>
    (‖coefficientWeyl C degree (α*(tupleProduct x:ℝ)*(x 0:ℝ)^2)‖/cap)^(2*power))]
  have hsum := positiveBox_reindex e bounds
    (fun x => (‖coefficientWeyl C degree (α*(tupleProduct x:ℝ)*(x i:ℝ)^2)‖/cap)^(2*power))
  rw [hsum]
  have hvol : tupleProduct (fun l => bounds (e l)) = tupleProduct bounds := e.prod_comp bounds
  rw [hvol]
  apply congrArg (fun v : ℝ => v/(tupleProduct bounds:ℝ))
  apply Finset.sum_congr rfl
  intro y hy
  have hp : tupleProduct (fun l => y (e.symm l)) = tupleProduct y := e.symm.prod_comp y
  have hi : e.symm i=0 := by rw [← he, e.symm_apply_apply]
  rw [hp]
  dsimp only
  rw [hi]

theorem other_volume_reindex {r : ℕ} (bounds : Fin (r+1) → ℕ)
    (hb : ∀ i, 0 < bounds i) (i : Fin (r+1))
    (e : Fin (r+1) ≃ Fin (r+1)) (he : e 0=i) :
    tupleProduct (fun l : Fin r => bounds (e l.succ)) =
      ∏ l ∈ Finset.univ.erase i, bounds l := by
  have ht := e.prod_comp bounds
  rw [Fin.prod_univ_succ, he] at ht
  rw [← Finset.mul_prod_erase Finset.univ bounds (Finset.mem_univ i)] at ht
  exact mul_left_cancel₀ (hb i).ne' ht

/-- Arbitrary distinguished-coordinate version, with the padded cutoff
compared directly with the actual product of all other coordinate bounds. -/
theorem coefficient_box_at_to_sample (r : ℕ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ P : ℝ, 1 ≤ P → ∀ bounds : Fin (r+1) → ℕ,
      (∀ l, 0 < bounds l) → ∀ i : Fin (r+1), ∀ J : ℕ,
      (∏ l ∈ Finset.univ.erase i, bounds l) ≤ J → (J:ℝ) ≤ P^B →
      ∀ Cpad : ℝ, (J:ℝ) ≤ Cpad*((∏ l ∈ Finset.univ.erase i, bounds l:ℕ):ℝ) →
      ∀ (C : Finset ℕ) (degree power : ℕ) (phi α : ℝ),
      coefficientBoxMomentAt bounds i C degree power (P^phi) α ≤
        D*Cpad*P^ε*NormalizedCoefficient.normalizedSampledCoefficient C degree power
          P phi (bounds i) J α (fun _ => 1) := by
  classical
  obtain ⟨D,hD,hgroup⟩ := coefficient_box_to_sample r hB hε
  refine ⟨D,hD,?_⟩
  intro P hP bounds hb i J hVJ hJP Cpad hpad C degree power phi α
  let e : Fin (r+1) ≃ Fin (r+1) := Equiv.swap 0 i
  have he : e 0=i := Equiv.swap_apply_left 0 i
  have hv := other_volume_reindex bounds hb i e he
  have HH := hgroup P hP (fun l => bounds (e l)) (fun l => hb (e l)) J
    (by simpa only [hv] using hVJ) hJP Cpad (by simpa only [hv] using hpad) C degree power phi α
  rw [coefficientBoxMomentAt_reindex bounds i e he]
  simpa only [he] using HH

#print axioms quadratic_second_box_to_sample
#print axioms quadratic_fourth_box_to_sample
#print axioms coefficient_box_to_sample
#print axioms coefficient_box_at_to_sample

end Waring.CartesianResourceMoments
