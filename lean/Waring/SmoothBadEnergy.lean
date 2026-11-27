import Waring.PrimeKernelCoefficient
import Waring.DivisorMarkedEnergy
import Waring.SmoothBadFactorCount
import Waring.PolicyCompletionGoodBlocks

/-!
# The actual bad-factor energy in efficient differencing

The finite cover n=d*y retains the prime kernel of y as a divisor mark on
the derivative value. After exact Fourier expansion, Cauchy separates the
divisor-marked auxiliary energy from the short-factor coefficient resource.
Both losses are already proved, giving O(M*Q*P^epsilon) times the original
auxiliary energy. Arbitrary remaining smooth tuples can be included in the
auxiliary index, without altering the statement or introducing a source
moment estimate as a hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SmoothBadEnergy
open SmoothMoments SmoothBadFactorCount PrimeSupportedCount PrimeKernelCoefficient
open ProductPairCount AuxiliaryL2Grouping PolicyCompletionHolder PolicyCompletionGoodBlocks

abbrev CoefficientIndex := (Σ _y : ℕ, ℕ)
abbrev ExpandedIndex (ι : Type*) := (Σ _r : ℕ, ι × CoefficientIndex)

def coefficientEndpoints (L N r : ℕ) : Finset CoefficientIndex :=
  (kernelFiber N r).sigma (fun y => shortFactors L N y)

def expandedEndpoints {ι : Type*} (K : Finset ℕ) (A : Finset ι)
    (D : ι → ℕ) (L N : ℕ) : Finset (ExpandedIndex ι) := by
  classical
  exact K.sigma (fun r => (A.filter (fun a => r ∣ D a)) ×ˢ coefficientEndpoints L N r)

def expandedFrequency {ι : Type*} (k : ℕ) (f : ι → ℤ) (x : ExpandedIndex ι) : ℤ :=
  f x.2.1 + (((x.2.2.2*x.2.2.1)^k : ℕ) : ℤ)

def coefficientSum (k L N r : ℕ) (α : ℝ) : ℂ :=
  ∑ y ∈ kernelFiber N r, ∑ d ∈ shortFactors L N y,
    fourier (((d*y)^k : ℕ) : ℤ) (α : AddCircle (1 : ℝ))

theorem expanded_frequencySum {ι : Type*} (k : ℕ) (K : Finset ℕ) (A : Finset ι)
    (f : ι → ℤ) (D : ι → ℕ) (L N : ℕ) (α : ℝ) :
    frequencySum (expandedEndpoints K A D L N) (expandedFrequency k f) α =
      ∑ r ∈ K, frequencySum (A.filter (fun a => r ∣ D a)) f α * coefficientSum k L N r α := by
  classical
  simp only [frequencySum,expandedEndpoints,expandedFrequency,coefficientEndpoints,
    coefficientSum,Finset.sum_sigma,Finset.sum_product,Finset.sum_mul,Finset.mul_sum,
    ← fourier_add]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_comm]

theorem expanded_frequencySum_square_le {ι : Type*} (k : ℕ) (K : Finset ℕ) (A : Finset ι)
    (f : ι → ℤ) (D : ι → ℕ) (L N : ℕ) (α : ℝ) :
    ‖frequencySum (expandedEndpoints K A D L N) (expandedFrequency k f) α‖^2 ≤
      (∑ r ∈ K, ‖frequencySum (A.filter (fun a => r ∣ D a)) f α‖^2) *
        (∑ r ∈ K, ‖coefficientSum k L N r α‖^2) := by
  classical
  rw [expanded_frequencySum]
  have hn := norm_sum_le K
    (fun r => frequencySum (A.filter (fun a => r ∣ D a)) f α * coefficientSum k L N r α)
  simp only [norm_mul] at hn
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq K
      (fun r => ‖frequencySum (A.filter (fun a => r ∣ D a)) f α‖)
      (fun r => ‖coefficientSum k L N r α‖))

/-- Exact orthogonality and Cauchy retain all frequency collisions. -/
theorem expanded_count_le_of_coefficient {ι : Type*} (k : ℕ)
    (K : Finset ℕ) (A : Finset ι) (f : ι → ℤ) (D : ι → ℕ) (L N : ℕ)
    (T : ℝ) (hT : ∀ α : ℝ, (∑ r ∈ K, ‖coefficientSum k L N r α‖^2) ≤ T) :
    ((collisionPairs (expandedEndpoints K A D L N) (expandedFrequency k f)).card : ℝ) ≤
      T * ∑ r ∈ K, ((collisionPairs (A.filter (fun a => r ∣ D a)) f).card : ℝ) := by
  classical
  have hleft := (continuous_frequencySum (expandedEndpoints K A D L N)
    (expandedFrequency k f)).norm.pow 2
  have hterm (r : ℕ) := (continuous_frequencySum (A.filter (fun a => r ∣ D a)) f).norm.pow 2
  have hright : Continuous (fun α : ℝ => T *
      ∑ r ∈ K, ‖frequencySum (A.filter (fun a => r ∣ D a)) f α‖^2) :=
    continuous_const.mul (continuous_finset_sum K (fun r _ => hterm r))
  calc
    _ = ∫ α in (0 : ℝ)..1,
        ‖frequencySum (expandedEndpoints K A D L N) (expandedFrequency k f) α‖^2 :=
      (interval_integral_sq_norm_eq_collision_count _ _).symm
    _ ≤ ∫ α in (0 : ℝ)..1, T *
        ∑ r ∈ K, ‖frequencySum (A.filter (fun a => r ∣ D a)) f α‖^2 := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (hleft.intervalIntegrable 0 1) (hright.intervalIntegrable 0 1)
      intro α hα
      exact (expanded_frequencySum_square_le k K A f D L N α).trans (by
        simpa only [mul_comm T] using mul_le_mul_of_nonneg_left (hT α)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finset_sum
        (fun r _ => (hterm r).intervalIntegrable 0 1)]
      simp_rw [frequencySum,interval_integral_sq_norm_eq_collision_count]
      rfl

/-- Both source losses are discharged for the full expanded bad family. -/
theorem expanded_count_le_rpow {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q M : ℝ), 1 ≤ Q → Q ≤ P → 1 ≤ M →
      ∀ (ι : Type*) (A : Finset ι) (f : ι → ℤ) (D : ι → ℕ),
      (∀ a ∈ A, 0 < D a ∧ (D a : ℝ) ≤ P^B) → ∀ k : ℕ,
      ((collisionPairs
        (expandedEndpoints (Finset.Icc 1 ⌊P^B⌋₊) A D ⌊M⌋₊ ⌊Q⌋₊)
        (expandedFrequency k f)).card : ℝ) ≤
        C*M*Q*P^ε*((collisionPairs A f).card : ℝ) := by
  classical
  let δ : ℝ := ε/2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨C₁,hC₁,hcoeff⟩ := kernel_coefficient_square_sum hB hδ
  obtain ⟨C₂,hC₂,hmark⟩ := DivisorMarkedEnergy.sum_marked_collision_le_rpow hB hδ
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro P Q M hQ hQP hM ι A f D hD k
  have hP : 1 ≤ P := hQ.trans hQP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  let K := Finset.Icc 1 ⌊P^B⌋₊
  have hK : ∀ r ∈ K, 0 < r ∧ (r : ℝ) ≤ P^B := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hrpos,hrP⟩
    exact ⟨hrpos,(by exact_mod_cast hrP : (r : ℝ) ≤ (⌊P^B⌋₊ : ℝ)).trans
      (Nat.floor_le (Real.rpow_nonneg hPpos.le B))⟩
  have hc : ∀ α : ℝ, (∑ r ∈ K, ‖coefficientSum k ⌊M⌋₊ ⌊Q⌋₊ r α‖^2) ≤
      C₁*M*Q*P^δ := by
    intro α
    exact hcoeff P Q M hQ hQP hM K hK
      (fun d y => fourier (((d*y)^k : ℕ) : ℤ) (α : AddCircle (1 : ℝ)))
      (fun _ _ => (Circle.norm_coe _).le)
  have hm := hmark P hP ι K A f D hD
  calc
    _ ≤ (C₁*M*Q*P^δ) *
        ∑ r ∈ K, ((collisionPairs (A.filter (fun a => r ∣ D a)) f).card : ℝ) :=
      expanded_count_le_of_coefficient k K A f D ⌊M⌋₊ ⌊Q⌋₊ _ hc
    _ ≤ (C₁*M*Q*P^δ) * (C₂*P^δ*((collisionPairs A f).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (C₁*C₂)*M*Q*P^ε*((collisionPairs A f).card : ℝ) := by
      have hp : P^δ*P^δ=P^ε := by
        rw [← Real.rpow_add hPpos]
        congr 1
        dsimp [δ]
        ring
      calc
        _ = (C₁*C₂)*M*Q*(P^δ*P^δ)*((collisionPairs A f).card : ℝ) := by ring
        _ = _ := by rw [hp]

def badEndpoints {ι : Type*} (A : Finset ι) (Q R M : ℝ) (D : ι → ℕ) :
    Finset (ι × ℕ) := by
  classical
  exact (A ×ˢ smoothNumbers Q R).filter (fun x => x.2 ∈ badSmoothNumbers Q R M (D x.1))

def restoreEndpoint {ι : Type*} (x : ExpandedIndex ι) : ι × ℕ :=
  (x.2.1,x.2.2.2*x.2.2.1)

/-- Every actual bad smooth endpoint is covered by a marked factorization. -/
theorem badEndpoints_covered {ι : Type*} (A : Finset ι) (P Q R M B : ℝ)
    (D : ι → ℕ) (hM : 1 ≤ M) (hP : 0 ≤ P)
    (hD : ∀ a ∈ A, 0 < D a ∧ (D a : ℝ) ≤ P^B) :
    ∀ x ∈ badEndpoints A Q R M D,
      ∃ y ∈ expandedEndpoints (Finset.Icc 1 ⌊P^B⌋₊) A D ⌊M⌋₊ ⌊Q⌋₊,
        restoreEndpoint y=x := by
  classical
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hx,hbad⟩
  rcases Finset.mem_product.mp hx with ⟨ha,hn⟩
  have hn0 : 0 < x.2 := (mem_smoothNumbers.mp hn).1.1
  have hnQ : x.2 ≤ ⌊Q⌋₊ := (mem_smoothNumbers.mp hn).1.2
  have hnot := (Finset.mem_filter.mp hbad).2
  rcases smooth_coprime_window_or_supported_quotient (b := D x.1) hn hM with
    ⟨d,u,hnu,hdM,hsupport⟩ | hgood
  · have hdpos : 0 < d := by
      by_contra h
      have hz : d=0 := by omega
      simp [hz] at hnu
      omega
    have hupos : 0 < u := by
      by_contra h
      have hz : u=0 := by omega
      simp [hz] at hnu
      omega
    have huQ : u ≤ ⌊Q⌋₊ := (Nat.le_of_dvd hn0 ⟨d,by rw [hnu,mul_comm]⟩).trans hnQ
    have hkerD := primeKernel_dvd_of_supported hupos (hD x.1 ha).1 hsupport
    have hkerP : (primeKernel u : ℝ) ≤ P^B :=
      (by exact_mod_cast Nat.le_of_dvd (hD x.1 ha).1 hkerD :
        (primeKernel u : ℝ) ≤ (D x.1 : ℝ)).trans (hD x.1 ha).2
    refine ⟨⟨primeKernel u,x.1,⟨u,d⟩⟩,?_,?_⟩
    · apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨primeKernel_pos u,Nat.le_floor hkerP⟩,?_⟩
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨ha,hkerD⟩,?_⟩
      apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hupos,huQ⟩,rfl⟩,?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos,Nat.le_floor hdM⟩,
        hnu ▸ hnQ⟩
    · exact Prod.ext rfl hnu.symm
  · exact (hnot hgood).elim

/-- The actual exceptional moment bound, with both arbitrary epsilon losses
proved and combined. Remaining smooth variables may be part of A. -/
theorem bad_collision_count_le_rpow {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q R M : ℝ), 1 ≤ Q → Q ≤ P → 1 ≤ M →
      ∀ (ι : Type*) (A : Finset ι) (f : ι → ℤ) (D : ι → ℕ),
      (∀ a ∈ A, 0 < D a ∧ (D a : ℝ) ≤ P^B) → ∀ k : ℕ,
      ((collisionPairs (badEndpoints A Q R M D)
        (fun x => f x.1 + ((x.2^k : ℕ) : ℤ))).card : ℝ) ≤
        C*M*Q*P^ε*((collisionPairs A f).card : ℝ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := expanded_count_le_rpow hB hε
  refine ⟨C,hC,?_⟩
  intro P Q R M hQ hQP hM ι A f D hD k
  have hcover := badEndpoints_covered A P Q R M B D hM
    ((zero_le_one.trans hQ).trans hQP) hD
  have hc := collision_card_le_of_cover (badEndpoints A Q R M D)
    (expandedEndpoints (Finset.Icc 1 ⌊P^B⌋₊) A D ⌊M⌋₊ ⌊Q⌋₊) restoreEndpoint
    (fun x => f x.1 + ((x.2^k : ℕ) : ℤ)) (expandedFrequency k f) hcover (fun _ _ => rfl)
  exact le_trans (by exact_mod_cast hc) (hbound P Q M hQ hQP hM ι A f D hD k)

#print axioms expanded_frequencySum
#print axioms expanded_count_le_rpow
#print axioms bad_collision_count_le_rpow
end Waring.SmoothBadEnergy
