import WaringSiegel.WSL2TraceResidueCharacters
import WaringSiegel.WSL2MomentKernelAverage

/-!
# Actual residue-restricted Weyl sums and finite trace-kernel averaging

All sums below use actual algebraic integers and their literal residue classes.
The Cauchy bound applies to the finite kernel average of the square.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField WaringSiegel.WSL2

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]
variable {α : Type*} [Fintype α]

def traceResidueWeylSum (a : 𝓞 K) (k : ℕ) (nodes : α → 𝓞 K) (w : α → ℂ)
    (r : PrincipalResidueRing a) (θ : ArchimedeanTraceTorus K) : ℂ :=
  ∑ i, if Ideal.Quotient.mk (Ideal.span {a}) (nodes i) = r then
    w i * traceTorusCharacter (nodes i ^ k) θ else 0

def traceCoprimeWeylSum (a : 𝓞 K) (k : ℕ) (nodes : α → 𝓞 K) (w : α → ℂ)
    (θ : ArchimedeanTraceTorus K) : ℂ :=
  ∑ i, if IsUnit (Ideal.Quotient.mk (Ideal.span {a}) (nodes i)) then
    w i * traceTorusCharacter (nodes i ^ k) θ else 0

theorem traceResidueWeylSum_translate (a : 𝓞 K) (k : ℕ)
    (nodes : α → 𝓞 K) (w : α → ℂ) (r : PrincipalResidueRing a)
    (θ : ArchimedeanTraceTorus K) (η : (traceTorusMul a).ker) :
    traceResidueWeylSum a k nodes w r (θ + η) =
      traceResidueWeylSum a k nodes w r θ * traceResidueAddChar a η (r ^ k) := by
  unfold traceResidueWeylSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : Ideal.Quotient.mk (Ideal.span {a}) (nodes i) = r
  · have hc : traceTorusCharacter (nodes i ^ k) η = traceResidueAddChar a η (r ^ k) := by
      rw [← h, ← map_pow, traceResidueAddChar_mk]
    simp only [if_pos h, traceTorusCharacter_add, hc, mul_assoc]
  · simp only [if_neg h, zero_mul]

theorem sum_units_eq_isUnit {Q : Type*} [CommRing Q] [Fintype Q] (x : Q) (z : ℂ) :
    (∑ u : Qˣ, if x = (u : Q) then z else 0) = if IsUnit x then z else 0 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simp only [Units.val_inj, Units.isUnit, ite_true]
    simp
  · have hneq (u : Qˣ) : x ≠ (u : Q) := fun h => hx (h ▸ u.isUnit)
    simp only [hneq, if_false, Finset.sum_const_zero, if_neg hx]

/-- The ordinary coprimality restriction is exactly the sum over unit residues. -/
theorem traceCoprimeWeylSum_eq_sum_residues (a : 𝓞 K)
    [Fintype (PrincipalResidueRing a)] (k : ℕ) (nodes : α → 𝓞 K)
    (w : α → ℂ) (θ : ArchimedeanTraceTorus K) :
    traceCoprimeWeylSum a k nodes w θ =
      ∑ r : (PrincipalResidueRing a)ˣ, traceResidueWeylSum a k nodes w r θ := by
  unfold traceResidueWeylSum traceCoprimeWeylSum
  rw [Finset.sum_comm]
  simp only [sum_units_eq_isUnit]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : IsUnit (Ideal.Quotient.mk (Ideal.span {a}) (nodes i))
  · simp only [if_pos h]
  · simp only [if_neg h]

theorem traceCoprimeWeylSum_translate (a : 𝓞 K)
    [Fintype (PrincipalResidueRing a)] (k : ℕ) (nodes : α → 𝓞 K)
    (w : α → ℂ) (θ : ArchimedeanTraceTorus K) (η : (traceTorusMul a).ker) :
    traceCoprimeWeylSum a k nodes w (θ + η) =
      finiteCharacterSum (fun r : (PrincipalResidueRing a)ˣ => (r : PrincipalResidueRing a)^k)
        (fun r => traceResidueWeylSum a k nodes w r θ) (traceResidueAddChar a η) := by
  rw [traceCoprimeWeylSum_eq_sum_residues]
  simp only [traceResidueWeylSum_translate, finiteCharacterSum]

/-- Exact finite averaging of the actual coprime Weyl sum. -/
theorem traceCoprimeWeylSum_kernel_average (a : 𝓞 K) (ha : a ≠ 0)
    [Fintype (PrincipalResidueRing a)] [Fintype (traceTorusMul a).ker]
    (k : ℕ) (nodes : α → 𝓞 K) (w : α → ℂ) (θ : ArchimedeanTraceTorus K) :
    (𝔼 η : (traceTorusMul a).ker, ‖traceCoprimeWeylSum a k nodes w (θ + η)‖^2) =
      ∑ b : PrincipalResidueRing a,
        ‖residueFiberSum (fun r : (PrincipalResidueRing a)ˣ => (r : PrincipalResidueRing a)^k)
          (fun r => traceResidueWeylSum a k nodes w r θ) b‖^2 := by
  simp only [traceCoprimeWeylSum_translate]
  exact finite_character_family_average_fibers _ _ (traceResidueAddChar a)
    (traceResidueAddChar_average a ha)

/-- Cauchy after averaging, with the exact unit-power kernel multiplicity. -/
theorem traceCoprimeWeylSum_kernel_average_le (a : 𝓞 K) (ha : a ≠ 0)
    [Fintype (PrincipalResidueRing a)] [Fintype (traceTorusMul a).ker]
    (k : ℕ) (nodes : α → 𝓞 K) (w : α → ℂ) (θ : ArchimedeanTraceTorus K) :
    (𝔼 η : (traceTorusMul a).ker, ‖traceCoprimeWeylSum a k nodes w (θ + η)‖^2) ≤
      ((unitPowerKernel (PrincipalResidueRing a) k).card : ℝ) *
        ∑ r : (PrincipalResidueRing a)ˣ, ‖traceResidueWeylSum a k nodes w r θ‖^2 := by
  simp only [traceCoprimeWeylSum_translate]
  exact finite_character_family_average_le _ _ (traceResidueAddChar a)
    (traceResidueAddChar_average a ha) _ (fun b => unit_power_fiber_card_le k b)

end WaringSiegel
