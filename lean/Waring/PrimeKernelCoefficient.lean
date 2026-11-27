import Waring.PrimeSupportedCount
import Waring.ProductPairCount
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The prime-kernel coefficient resource in the exceptional branch

Group y by the product of its distinct prime factors. Each group has
P^epsilon many y when its kernel is polynomially bounded in P. Finite
Cauchy, the short-factor cutoff, and the proved divisor sum bound yield
the source M*Q*P^epsilon estimate uniformly in every coefficient phase.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PrimeKernelCoefficient
open PrimeSupportedCount ProductPairCount

def primeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

def kernelFiber (N r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun y => primeKernel y=r)

theorem primeKernel_pos (n : ℕ) : 0 < primeKernel n :=
  Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)

theorem primeKernel_dvd (n : ℕ) : primeKernel n ∣ n := Nat.prod_primeFactors_dvd n

theorem isPrimeSupported_kernel {n : ℕ} (hn : 0 < n) :
    IsPrimeSupported n (primeKernel n) := by
  intro p hp hpn
  apply Finset.dvd_prod_of_mem
  exact Nat.mem_primeFactors.mpr ⟨hp,hpn,hn.ne'⟩

theorem primeKernel_dvd_of_supported {n D : ℕ} (hn : 0 < n) (hD : 0 < D)
    (hs : IsPrimeSupported n D) : primeKernel n ∣ D := by
  have hsub : n.primeFactors ⊆ D.primeFactors := by
    intro p hp
    have hpn := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hpn.1,hs p hpn.1 hpn.2.1,hD.ne'⟩
  exact (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hsub).trans (primeKernel_dvd D)

theorem kernelFiber_subset_supported {N L r : ℕ} (hNL : N ≤ L) :
    kernelFiber N r ⊆ supportedNumbers L r := by
  classical
  intro y hy
  rcases Finset.mem_filter.mp hy with ⟨hy,hker⟩
  rcases Finset.mem_Icc.mp hy with ⟨hy1,hyN⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hy1,hyN.trans hNL⟩,
    hker ▸ isPrimeSupported_kernel hy1⟩

/-- Finite Cauchy on one actual prime-kernel class. -/
theorem coefficient_square_le (L N r : ℕ) (a : ℕ → ℕ → ℂ)
    (ha : ∀ d y, ‖a d y‖ ≤ 1) :
    ‖∑ y ∈ kernelFiber N r, ∑ d ∈ shortFactors L N y, a d y‖^2 ≤
      ((kernelFiber N r).card : ℝ)*(L : ℝ)*
        ∑ y ∈ kernelFiber N r, ((shortFactors L N y).card : ℝ) := by
  classical
  have hnorm : ‖∑ y ∈ kernelFiber N r, ∑ d ∈ shortFactors L N y, a d y‖ ≤
      ∑ y ∈ kernelFiber N r, ((shortFactors L N y).card : ℝ) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro y hy
    exact (norm_sum_le _ _).trans (by
      simpa using Finset.sum_le_sum (s := shortFactors L N y) (fun d _ => ha d y))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (kernelFiber N r)
    (fun _ => (1 : ℝ)) (fun y => ((shortFactors L N y).card : ℝ))
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  calc
    _ ≤ (∑ y ∈ kernelFiber N r, ((shortFactors L N y).card : ℝ))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ ((kernelFiber N r).card : ℝ)*
        ∑ y ∈ kernelFiber N r, ((shortFactors L N y).card : ℝ)^2 := hcs
    _ ≤ ((kernelFiber N r).card : ℝ)*
        ∑ y ∈ kernelFiber N r, (L : ℝ)*((shortFactors L N y).card : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro y hy
      have hc : ((shortFactors L N y).card : ℝ) ≤ L := by
        exact_mod_cast (show (shortFactors L N y).card ≤ L from by
          simpa using Finset.card_filter_le (Finset.Icc 1 L) (fun d => d*y ≤ N))
      nlinarith [show (0 : ℝ) ≤ (shortFactors L N y).card by positivity]
    _ = _ := by rw [← Finset.mul_sum,mul_assoc]

/-- Kernel classes are disjoint, even if only some kernels are retained. -/
theorem sum_kernel_fibers_le (K : Finset ℕ) (N : ℕ) (b : ℕ → ℝ)
    (hb : ∀ y ∈ Finset.Icc 1 N, 0 ≤ b y) :
    (∑ r ∈ K, ∑ y ∈ kernelFiber N r, b y) ≤ ∑ y ∈ Finset.Icc 1 N, b y := by
  classical
  simp only [kernelFiber,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro y hy
  simp only [Finset.sum_ite_eq]
  split_ifs <;> simp_all

/-- An actual uniform bound for all prime-kernel coefficient sums. -/
theorem kernel_coefficient_square_sum {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P Q M : ℝ, 1 ≤ Q → Q ≤ P → 1 ≤ M →
      ∀ K : Finset ℕ, (∀ r ∈ K, 0 < r ∧ (r : ℝ) ≤ P^B) →
      ∀ a : ℕ → ℕ → ℂ, (∀ d y, ‖a d y‖ ≤ 1) →
      (∑ r ∈ K, ‖∑ y ∈ kernelFiber ⌊Q⌋₊ r,
        ∑ d ∈ shortFactors ⌊M⌋₊ ⌊Q⌋₊ y, a d y‖^2) ≤ C*M*Q*P^ε := by
  let δ : ℝ := ε/2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨C₁,hC₁,hfiber⟩ := supportedNumbers_polynomial_scale
    (A := (1 : ℝ)) (by norm_num) hB hδ
  obtain ⟨C₂,hC₂,hpairs⟩ := factorPairs_card_le_cutoff hδ
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro P Q M hQ hQP hM K hK a ha
  have hP : 1 ≤ P := hQ.trans hQP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hMP : (⌊M⌋₊ : ℝ) ≤ M := Nat.floor_le (zero_le_one.trans hM)
  have hY : ∀ r ∈ K, ((kernelFiber ⌊Q⌋₊ r).card : ℝ) ≤ C₁*P^δ := by
    intro r hr
    have hsub := kernelFiber_subset_supported (r := r) (Nat.floor_mono hQP)
    have hc : ((kernelFiber ⌊Q⌋₊ r).card : ℝ) ≤
        ((supportedNumbers ⌊P⌋₊ r).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    apply hc.trans
    simpa only [Real.rpow_one] using hfiber P hP r (hK r hr).1 (hK r hr).2
  have htotal : (∑ r ∈ K, ∑ y ∈ kernelFiber ⌊Q⌋₊ r,
      ((shortFactors ⌊M⌋₊ ⌊Q⌋₊ y).card : ℝ)) ≤ C₂*Q*P^δ := by
    calc
      _ ≤ ∑ y ∈ Finset.Icc 1 ⌊Q⌋₊, ((shortFactors ⌊M⌋₊ ⌊Q⌋₊ y).card : ℝ) :=
        sum_kernel_fibers_le K _ _ (fun _ _ => by positivity)
      _ = ((factorPairs ⌊M⌋₊ ⌊Q⌋₊).card : ℝ) := by
        exact_mod_cast (factorPairs_card_eq_sum ⌊M⌋₊ ⌊Q⌋₊).symm
      _ ≤ C₂*Q*Q^δ := hpairs Q hQ ⌊M⌋₊
      _ ≤ C₂*Q*P^δ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (zero_le_one.trans hQ) hQP hδ.le) (by positivity)
  calc
    _ ≤ ∑ r ∈ K, (C₁*P^δ)*M*
        ∑ y ∈ kernelFiber ⌊Q⌋₊ r, ((shortFactors ⌊M⌋₊ ⌊Q⌋₊ y).card : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hmult : ((kernelFiber ⌊Q⌋₊ r).card : ℝ)*(⌊M⌋₊ : ℝ) ≤ (C₁*P^δ)*M :=
        mul_le_mul (hY r hr) hMP (Nat.cast_nonneg _) (mul_nonneg hC₁.le (Real.rpow_nonneg hPpos.le _))
      have hsum : 0 ≤ ∑ y ∈ kernelFiber ⌊Q⌋₊ r,
          ((shortFactors ⌊M⌋₊ ⌊Q⌋₊ y).card : ℝ) :=
        Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      exact (coefficient_square_le ⌊M⌋₊ ⌊Q⌋₊ r a ha).trans
        (mul_le_mul_of_nonneg_right hmult hsum)
    _ = (C₁*P^δ)*M*(∑ r ∈ K, ∑ y ∈ kernelFiber ⌊Q⌋₊ r,
        ((shortFactors ⌊M⌋₊ ⌊Q⌋₊ y).card : ℝ)) := (Finset.mul_sum ..).symm
    _ ≤ (C₁*P^δ)*M*(C₂*Q*P^δ) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = (C₁*C₂)*M*Q*P^ε := by
      have hp : P^δ*P^δ=P^ε := by
        rw [← Real.rpow_add hPpos]
        congr 1
        dsimp [δ]
        ring
      calc
        _ = (C₁*C₂)*M*Q*(P^δ*P^δ) := by ring
        _ = _ := by rw [hp]

#print axioms primeKernel_dvd_of_supported
#print axioms coefficient_square_le
#print axioms kernel_coefficient_square_sum
end Waring.PrimeKernelCoefficient
