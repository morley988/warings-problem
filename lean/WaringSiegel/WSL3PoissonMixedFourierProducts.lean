import WaringSiegel.WSL3PoissonMixedJExpansion

/-! # Actual trace Fourier products for the weighted mixed solution count -/
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory NumberField WaringSiegel.WSL2
open scoped NumberField BigOperators Classical ComplexConjugate
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem traceTorusCharacter_add_frequency (x y : 𝓞 K) (q : ArchimedeanTraceTorus K) :
    traceTorusCharacter (x+y) q = traceTorusCharacter x q*traceTorusCharacter y q := by
  simp only [traceTorusCharacter,map_add,latticeCharacter_add]

def traceFrequencySum {α : Type*} [Fintype α] (f : α → 𝓞 K) (w : α → ℂ)
    (q : ArchimedeanTraceTorus K) : ℂ :=
  ∑ a, w a*traceTorusCharacter (f a) q

theorem traceFrequencySum_mul {α β : Type*} [Fintype α] [Fintype β]
    (f : α → 𝓞 K) (g : β → 𝓞 K) (w : α → ℂ) (v : β → ℂ)
    (q : ArchimedeanTraceTorus K) :
    traceFrequencySum f w q*traceFrequencySum g v q =
      traceFrequencySum (fun p : α × β => f p.1+g p.2) (fun p => w p.1*v p.2) q := by
  simp only [traceFrequencySum,Fintype.sum_prod_type,Finset.sum_mul_sum,traceTorusCharacter_add_frequency]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem traceWeylSum_mul_eq_traceFrequencySum {α : Type*} [Fintype α]
    (k : ℕ) (f : α → 𝓞 K) (w : α → ℂ) (d : 𝓞 K) (q : ArchimedeanTraceTorus K) :
    traceWeylSum k f w (traceTorusMul d q) =
      traceFrequencySum (fun a => d*f a^k) w q := by
  simp only [traceWeylSum,traceFrequencySum,traceTorusCharacter_mul]

theorem traceFrequencySum_mul_arg {α : Type*} [Fintype α]
    (f : α → 𝓞 K) (w : α → ℂ) (d : 𝓞 K) (q : ArchimedeanTraceTorus K) :
    traceFrequencySum f w (traceTorusMul d q) =
      traceFrequencySum (fun a => d*f a) w q := by
  simp only [traceFrequencySum,traceTorusCharacter_mul]

theorem traceWeylSum_norm_fourth_expansion {α : Type*} [Fintype α]
    (k : ℕ) (f : α → 𝓞 K) (w : α → ℂ) (q : ArchimedeanTraceTorus K) :
    ((‖traceWeylSum k f w q‖^4:ℝ):ℂ) =
      traceFrequencySum
        (fun p : (α×α)×(α×α) => (f p.1.1^k-f p.1.2^k)+(f p.2.1^k-f p.2.2^k))
        (fun p => (w p.1.1*conj (w p.1.2))*(w p.2.1*conj (w p.2.2))) q := by
  have h2 : ((‖traceWeylSum k f w q‖^2:ℝ):ℂ) =
      traceFrequencySum (fun p : α×α => f p.1^k-f p.2^k)
        (fun p => w p.1*conj (w p.2)) q := by
    rw [Complex.ofReal_pow,← Complex.mul_conj']
    exact traceWeylSum_mul_conj_expansion _ _ _ _ _ _
  have h4 : ((‖traceWeylSum k f w q‖^4:ℝ):ℂ) =
      ((‖traceWeylSum k f w q‖^2:ℝ):ℂ)*((‖traceWeylSum k f w q‖^2:ℝ):ℂ) := by
    simp only [Complex.ofReal_pow]
    ring
  rw [h4,h2,traceFrequencySum_mul]

theorem traceFrequencySum_integral {α : Type*} [Fintype α]
    (f : α → 𝓞 K) (w : α → ℂ) :
    (∫ q, traceFrequencySum f w q ∂traceHaar) =
      ∑ a, if f a=0 then w a else 0 := by
  unfold traceFrequencySum
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_const_mul,traceTorusCharacter_integral]
    split_ifs <;> simp
  · intro a _
    exact (continuous_const.mul (traceTorusCharacter_continuous _)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem traceFrequencySum_sum {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → 𝓞 K) (w : α → β → ℂ) (q : ArchimedeanTraceTorus K) :
    (∑ a : α, traceFrequencySum (f a) (w a) q) =
      traceFrequencySum (fun p : α×β => f p.1 p.2) (fun p => w p.1 p.2) q := by
  simp only [traceFrequencySum,Fintype.sum_prod_type]

theorem traceFrequencySum_const_mul {α : Type*} [Fintype α]
    (f : α → 𝓞 K) (w : α → ℂ) (c : ℂ) (q : ArchimedeanTraceTorus K) :
    c*traceFrequencySum f w q = traceFrequencySum f (fun a => c*w a) q := by
  simp only [traceFrequencySum,Finset.mul_sum,mul_assoc]

end WaringSiegel.WSL3Poisson
