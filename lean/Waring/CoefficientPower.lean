import Waring.EvenMoments
import Waring.FourierCompletion
import Waring.CubicSamplingAsymptotic

/-!
# Actual coefficients of powers of the manuscript's smooth block sums

The coefficients below are literal finite tuple counts. Their finite support,
Fourier expansion and Parseval energy are proved. The degree-sixteen or
degree-eighteen smooth moment can therefore be supplied as an explicit
analytic input; the published admissibility statements are not asserted here.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Waring.CoefficientPower
open SmoothMoments QuadraticModulation FourierCompletion
open SampledLinearSecondMoment CubicCoefficientSampling

/-- The manuscript's actual smooth coefficient block. -/
def coefficientBlock (P R M : ℝ) : Finset ℕ :=
  (smoothNumbers P R).filter (fun m => M < (m : ℝ) ∧ (m : ℝ) ≤ M*R)

theorem coefficientBlock_subset (P R M : ℝ) :
    coefficientBlock P R M ⊆ smoothNumbers (M*R) R := by
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hm, hlo, hhi⟩
  rcases mem_smoothNumbers.mp hm with ⟨⟨hpos, _⟩, hs⟩
  exact mem_smoothNumbers.mpr ⟨⟨hpos, Nat.le_floor hhi⟩, hs⟩

/-- A degree-k coefficient sum over an arbitrary actual finite block. -/
def coefficientWeyl (A : Finset ℕ) (k : ℕ) (β : ℝ) : ℂ :=
  ∑ m ∈ A, e (β*(m : ℝ)^k)

theorem e_nat_frequency (β : ℝ) (n : ℕ) :
    e (β*(n : ℝ)) = fourier (n : ℤ) (β : AddCircle (1 : ℝ)) := by
  simpa only [e, Int.cast_natCast] using exp_linear_eq_fourier β (n : ℤ)

theorem coefficientWeyl_eq_fourier (A : Finset ℕ) (k : ℕ) (β : ℝ) :
    coefficientWeyl A k β = ∑ m ∈ A, fourier ((m^k : ℕ) : ℤ) (β : AddCircle (1 : ℝ)) := by
  unfold coefficientWeyl
  apply Finset.sum_congr rfl
  intro m _
  simpa only [Nat.cast_pow] using e_nat_frequency β (m^k)

/-- Coefficient of frequency n in the r-th power, as an actual tuple count. -/
def powerCoefficient (A : Finset ℕ) (k r n : ℕ) : ℂ :=
  (((finiteTuples A r).filter (fun f => ∑ i, f i ^ k = n)).card : ℂ)

/-- The endpoint is included by the explicit +1 in the range length. -/
def supportLength (k r M : ℕ) : ℕ := r*M^k+1

theorem tuple_frequency_lt {A : Finset ℕ} {k r M : ℕ}
    (hA : ∀ m ∈ A, m ≤ M) {f : Fin r → ℕ} (hf : f ∈ finiteTuples A r) :
    (∑ i, f i ^ k) < supportLength k r M := by
  have hmem : ∀ i, f i ∈ A := Fintype.mem_piFinset.mp hf
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
    (fun i _ => Nat.pow_le_pow_left (hA (f i) (hmem i)) k)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    supportLength] using Nat.lt_succ_of_le hsum

/-- Finite Fourier expansion of the actual r-th power. -/
theorem coefficientWeyl_pow (A : Finset ℕ) (k r M : ℕ)
    (hA : ∀ m ∈ A, m ≤ M) (β : ℝ) :
    coefficientWeyl A k β ^ r =
      ∑ n ∈ Finset.range (supportLength k r M), powerCoefficient A k r n * e (β*(n : ℝ)) := by
  classical
  rw [coefficientWeyl_eq_fourier, sum_pow_fourier]
  have hmap : ∀ f ∈ finiteTuples A r, (∑ i, f i ^ k) ∈ Finset.range (supportLength k r M) :=
    fun f hf => Finset.mem_range.mpr (tuple_frequency_lt hA hf)
  have H := Finset.sum_fiberwise_of_maps_to' hmap
    (fun n : ℕ => fourier (n : ℤ) (β : AddCircle (1 : ℝ)))
  have hh (f : Fin r → ℕ) : (∑ i, ((f i ^ k : ℕ) : ℤ)) = ((∑ i, f i ^ k : ℕ) : ℤ) := by simp
  simp_rw [hh]
  rw [← H]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Finset.sum_const, nsmul_eq_mul, powerCoefficient, e_nat_frequency]

/-- Parseval for arbitrary weighted integer frequencies, proved by exact
coefficient extraction. -/
theorem weighted_parseval (S : Finset ℤ) (w : ℤ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖modulatedSum S w t‖ ^ 2) = ∑ n ∈ S, ‖w n‖ ^ 2 := by
  have hpoint (t : ℝ) : ((‖modulatedSum S w t‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ S, conj (w n) * (modulatedSum S w t * fourier (-n) (t : AddCircle (1 : ℝ))) := by
    have hconj : conj (modulatedSum S w t) =
        ∑ n ∈ S, conj (w n) * fourier (-n) (t : AddCircle (1 : ℝ)) := by
      simp only [modulatedSum, map_sum, map_mul, fourier_neg]
    rw [Complex.ofReal_pow, ← Complex.mul_conj', hconj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hi (n : ℤ) : IntervalIntegrable (fun t : ℝ =>
      conj (w n) * (modulatedSum S w t * fourier (-n) (t : AddCircle (1 : ℝ)))) volume 0 1 :=
    (continuous_const.mul ((continuous_modulatedSum S w).mul
      ((fourier (-n)).continuous.comp (AddCircle.continuous_mk' 1)))).intervalIntegrable 0 1
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finset_sum (fun n _ => hi n), Complex.ofReal_sum]
  simp_rw [intervalIntegral.integral_const_mul, coefficient_extraction]
  apply Finset.sum_congr rfl
  intro n hn
  rw [if_pos hn, Complex.ofReal_pow, ← Complex.mul_conj']
  ring

/-- Nat-indexed Parseval, in the exact convention used by cubicSecondMoment. -/
theorem coefficientEnergy_eq_integral (N : ℕ) (c : ℕ → ℂ) :
    coefficientEnergy N c =
      ∫ t in (0 : ℝ)..1, ‖∑ n ∈ Finset.range N, c n * e (t*(n : ℝ))‖ ^ 2 := by
  let S : Finset ℤ := (Finset.range N).image (fun n : ℕ => (n : ℤ))
  have heq (t : ℝ) : modulatedSum S (fun n => c n.toNat) t =
      ∑ n ∈ Finset.range N, c n * e (t*(n : ℝ)) := by
    unfold modulatedSum S
    rw [Finset.sum_image]
    · simp only [Int.toNat_natCast, e_nat_frequency]
    · intro i _ j _ hij
      exact Int.ofNat.inj hij
  have henergy : (∑ n ∈ S, ‖c n.toNat‖^2) = coefficientEnergy N c := by
    unfold S coefficientEnergy
    rw [Finset.sum_image]
    · simp only [Int.toNat_natCast]
    · intro i _ j _ hij
      exact Int.ofNat.inj hij
  have H := weighted_parseval S (fun n => c n.toNat)
  simp_rw [heq] at H
  rw [henergy] at H
  exact H.symm

/-- The coefficient energy is exactly the actual even moment of the block. -/
theorem powerCoefficient_energy (A : Finset ℕ) (k r M : ℕ)
    (hA : ∀ m ∈ A, m ≤ M) :
    coefficientEnergy (supportLength k r M) (powerCoefficient A k r) =
      frequencyEvenMoment A (fun m => ((m^k : ℕ) : ℤ)) r := by
  rw [coefficientEnergy_eq_integral]
  simp_rw [← coefficientWeyl_pow A k r M hA, norm_pow, ← pow_mul, Nat.mul_comm r 2,
    coefficientWeyl_eq_fourier]
  rfl

/-- The manuscript's coefficient-energy inequality is a genuine even-moment
subset inequality, not a false pointwise bound for a subsum. -/
theorem powerCoefficient_energy_le_smoothMoment (A : Finset ℕ) (k r : ℕ) (X R : ℝ)
    (hA : A ⊆ smoothNumbers X R) :
    coefficientEnergy (supportLength k r ⌊X⌋₊) (powerCoefficient A k r) ≤
      smoothMoment k (2*r) X R := by
  rw [powerCoefficient_energy A k r ⌊X⌋₊
    (fun m hm => (mem_smoothNumbers.mp (hA hm)).1.2), smoothMoment_even_eq_frequency]
  exact frequencyEvenMoment_mono hA _ r

/-- Literal identification of the sampled even block moment with the proved
cubic sampling operator. The sampling shifts may depend arbitrarily on h. -/
theorem sampled_power_eq_cubicSecondMoment (A : Finset ℕ) (k r M H J : ℕ)
    (hA : ∀ m ∈ A, m ≤ M) (α : ℝ) (σ : ℕ → ℝ) :
    (∑ h ∈ Finset.Icc 1 H, ∑ j ∈ Finset.range J,
      ‖coefficientWeyl A k (α*(h:ℝ)^3*((j:ℝ)+σ h))‖ ^ (2*r)) =
      cubicSecondMoment α H (supportLength k r M) J (powerCoefficient A k r) σ := by
  unfold cubicSecondMoment
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro j _
  rw [← coefficientWeyl_pow A k r M hA, norm_pow, ← pow_mul, Nat.mul_comm r 2]

/-- The proved sampling estimate applied to the actual even power of a
smooth coefficient block. The full smooth moment remains displayed, so a
published moment estimate must be supplied explicitly when it is used. -/
theorem coefficient_sampling_epsilon {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ (A : Finset ℕ) (k r : ℕ) (X R : ℝ),
      A ⊆ smoothNumbers X R → ∀ H J : ℕ, 0 < H → 0 < J →
      (H:ℝ)^3*((supportLength k r ⌊X⌋₊ : ℝ)*J) ≤ P^B →
      ∀ (α : ℝ) (σ : ℕ → ℝ),
        (∑ h ∈ Finset.Icc 1 H, ∑ j ∈ Finset.range J,
          ‖coefficientWeyl A k (α*(h:ℝ)^3*((j:ℝ)+σ h))‖ ^ (2*r)) ≤
          C*P^ε*(H:ℝ)*((supportLength k r ⌊X⌋₊ : ℝ)*J)*
            smoothMoment k (2*r) X R * samplingShape H (supportLength k r ⌊X⌋₊) J α := by
  obtain ⟨C,hC,hbound⟩ := cubic_sampling_epsilon hB hε
  refine ⟨C,hC,?_⟩
  intro P hP A k r X R hA H J hH hJ hV α σ
  have hN : 0 < supportLength k r ⌊X⌋₊ := by unfold supportLength; omega
  have hAm : ∀ m ∈ A, m ≤ ⌊X⌋₊ := fun m hm => (mem_smoothNumbers.mp (hA hm)).1.2
  rw [sampled_power_eq_cubicSecondMoment A k r ⌊X⌋₊ H J hAm α σ]
  apply (hbound P hP H (supportLength k r ⌊X⌋₊) J hH hN hJ hV α
    (powerCoefficient A k r) σ).trans
  have hshape := samplingShape_nonneg H (supportLength k r ⌊X⌋₊) J α
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  apply mul_le_mul_of_nonneg_right _ hshape
  apply mul_le_mul_of_nonneg_left (powerCoefficient_energy_le_smoothMoment A k r X R hA)
  positivity

/-- Supplying an actual admissibility theorem bounds the coefficient energy
with its full uniform smoothness quantifiers. No seed theorem is postulated. -/
theorem coefficient_energy_of_admissible {k r : ℕ} {lam : ℝ}
    (h : AdmissibleExponent k (2*r) lam) {ε : ℝ} (hε : 0 < ε) :
    ∃ η C P₀ : ℝ, 0 < η ∧ 0 < C ∧ 1 ≤ P₀ ∧
      ∀ X : ℝ, P₀ ≤ X → ∀ R : ℝ, 1 ≤ R → R ≤ X^η →
        ∀ A : Finset ℕ, A ⊆ smoothNumbers X R →
          coefficientEnergy (supportLength k r ⌊X⌋₊) (powerCoefficient A k r) ≤ C*X^(lam+ε) := by
  obtain ⟨η,hη,C,hC,P₀,hP₀,hbound⟩ := h ε hε
  refine ⟨η,C,P₀,hη,hC,hP₀,?_⟩
  intro X hX R hR hRX A hA
  exact (powerCoefficient_energy_le_smoothMoment A k r X R hA).trans (hbound X hX R hR hRX)

/-- Padded support whose real size is bounded below without a floor loss. -/
def paddedSupport (k r : ℕ) (X : ℝ) : ℕ := supportLength k r ⌈X⌉₊

theorem paddedSupport_pos (k r : ℕ) (X : ℝ) : 0 < paddedSupport k r X := by
  unfold paddedSupport supportLength
  omega

theorem paddedSupport_bounds (k r : ℕ) {X : ℝ} (hX : 1 ≤ X) (hr : 1 ≤ r) :
    X^k ≤ (paddedSupport k r X : ℝ) ∧
      (paddedSupport k r X : ℝ) ≤ ((r : ℝ)+1)*(2*X)^k := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hlo : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
  have hhi : (⌈X⌉₊ : ℝ) ≤ 2*X := by
    have hh := Nat.ceil_lt_add_one hX0
    linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpow0 : 0 ≤ (⌈X⌉₊ : ℝ)^k := by positivity
  have hpow1 : (1 : ℝ) ≤ (2*X)^k := one_le_pow₀ (by linarith : (1:ℝ) ≤ 2*X)
  unfold paddedSupport supportLength
  push_cast
  constructor
  · have hh := pow_le_pow_left₀ hX0 hlo k
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hpow0]
  · have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ⌈X⌉₊) hhi k)
      (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    nlinarith

theorem powerCoefficient_padded_energy_le_smoothMoment (A : Finset ℕ) (k r : ℕ) (X R : ℝ)
    (hA : A ⊆ smoothNumbers X R) :
    coefficientEnergy (paddedSupport k r X) (powerCoefficient A k r) ≤ smoothMoment k (2*r) X R := by
  rw [paddedSupport, powerCoefficient_energy A k r ⌈X⌉₊
    (fun m hm => (mem_smoothNumbers.mp (hA hm)).1.2.trans (Nat.floor_le_ceil X)),
    smoothMoment_even_eq_frequency]
  exact frequencyEvenMoment_mono hA _ r

/-- Same actual coefficient estimate with padded support, directly suited to
lower scale bounds in the four-cap resource theorem. -/
theorem coefficient_sampling_padded_epsilon {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ (A : Finset ℕ) (k r : ℕ) (X R : ℝ),
      A ⊆ smoothNumbers X R → ∀ H J : ℕ, 0 < H → 0 < J →
      (H:ℝ)^3*((paddedSupport k r X : ℝ)*J) ≤ P^B →
      ∀ (α : ℝ) (σ : ℕ → ℝ),
        (∑ h ∈ Finset.Icc 1 H, ∑ j ∈ Finset.range J,
          ‖coefficientWeyl A k (α*(h:ℝ)^3*((j:ℝ)+σ h))‖ ^ (2*r)) ≤
          C*P^ε*(H:ℝ)*((paddedSupport k r X : ℝ)*J)*
            smoothMoment k (2*r) X R * samplingShape H (paddedSupport k r X) J α := by
  obtain ⟨C,hC,hbound⟩ := cubic_sampling_epsilon hB hε
  refine ⟨C,hC,?_⟩
  intro P hP A k r X R hA H J hH hJ hV α σ
  have hAm : ∀ m ∈ A, m ≤ ⌈X⌉₊ :=
    fun m hm => (mem_smoothNumbers.mp (hA hm)).1.2.trans (Nat.floor_le_ceil X)
  rw [sampled_power_eq_cubicSecondMoment A k r ⌈X⌉₊ H J hAm α σ]
  apply (hbound P hP H (paddedSupport k r X) J hH (paddedSupport_pos k r X) hJ hV α
    (powerCoefficient A k r) σ).trans
  have hshape := samplingShape_nonneg H (paddedSupport k r X) J α
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  apply mul_le_mul_of_nonneg_right _ hshape
  apply mul_le_mul_of_nonneg_left (powerCoefficient_padded_energy_le_smoothMoment A k r X R hA)
  positivity

#print axioms coefficientWeyl_pow
#print axioms powerCoefficient_energy_le_smoothMoment
#print axioms sampled_power_eq_cubicSecondMoment
#print axioms coefficient_sampling_epsilon
#print axioms coefficient_energy_of_admissible
#print axioms paddedSupport_bounds
#print axioms coefficient_sampling_padded_epsilon

end Waring.CoefficientPower
