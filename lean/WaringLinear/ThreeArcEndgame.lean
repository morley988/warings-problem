import WaringLinear.AnnulusPruning
import WaringLinear.MixedTarget
import WaringSiegel.WSL2MomentCubicWeyl

/-! # A three-arc endgame for bounded, totally positive field representations -/
noncomputable section
open MeasureTheory
open scoped NumberField BigOperators ComplexConjugate
open WaringSiegel WaringSiegel.WSL2
namespace WaringLinear

variable {X : Type*} [MeasurableSpace X]

/-- On the outer minor arcs the a ordinary factors have a uniform saving.
The restricted factors are disposed of using an m-th moment and d trivial bounds. -/
theorem outer_minor_bound (μ : Measure X) (E : Set X) (hE : MeasurableSet E)
    (f F : X → ℝ) (hf : ∀ x, 0≤f x) (hF : ∀ x, 0≤F x)
    (a m d : ℕ) (C P D : ℝ) (hC : 0≤C) (hP : 0≤P)
    (hminor : ∀ x∈E, f x≤C) (hbox : ∀ x∈E, F x≤P)
    (hI : Integrable (fun x => f x^a*F x^(m+d)) μ)
    (hM : Integrable (fun x => F x^m) μ) (hmom : (∫ x, F x^m ∂μ)≤D) :
    (∫ x in E, f x^a*F x^(m+d) ∂μ) ≤ C^a*P^d*D := by
  have hbound : (∫ x in E, f x^a*F x^(m+d) ∂μ) ≤ C^a*P^d*(∫ x in E, F x^m ∂μ) := by
    rw [←integral_const_mul]
    apply setIntegral_mono_on hI.integrableOn (hM.const_mul _).integrableOn hE
    intro x hx
    rw [pow_add]
    have hb := mul_le_mul (pow_le_pow_left₀ (hf x) (hminor x hx) a)
      (pow_le_pow_left₀ (hF x) (hbox x hx) d) (pow_nonneg (hF x) _) (pow_nonneg hC _)
    calc
      _ = (f x^a*F x^d)*F x^m := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (pow_nonneg (hF x) _)
  exact hbound.trans (mul_le_mul_of_nonneg_left
    ((setIntegral_le_integral hM (Filter.Eventually.of_forall (fun x => pow_nonneg (hF x) _))).trans
      hmom) (by positivity))

variable {K : Type*} [Field K] [NumberField K] {α β : Type*} [Fintype α] [Fintype β]

abbrev CoordTorus (K : Type*) [Field K] [NumberField K] :=
  NumberFieldCoordinateIndex K → AddCircle (1:ℝ)

def fieldPowerSum (k : ℕ) (n : α → 𝓞 K) (w : α → ℂ) (θ : CoordTorus K) : ℂ :=
  frequencySum (fun i => integerCoordinates K ((n i)^k)) w θ

local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : IsProbabilityMeasure (latticeHaar (ι := NumberFieldCoordinateIndex K)) := by
  unfold latticeHaar
  infer_instance

/-- A positive core main term with a sufficiently small annular and outer
error gives an actual totally-positive representation at scale C. -/
theorem positive_field_target_from_arc_estimates (k a m d : ℕ) (hS : 0<a+(m+d))
    (x : α → 𝓞 K) (y : β → 𝓞 K) (w : α → ℂ) (v : β → ℂ) (ν : 𝓞 K) (C : ℝ)
    (hx : ∀ i, x i≠0 ∧ TotallyPositive (x i)) (hy : ∀ j, y j≠0 ∧ TotallyPositive (y j))
    (hxb : ∀ i, absNorm (x i)≤C*absNorm ν^(1/(k:ℝ)))
    (hyb : ∀ i, absNorm (y i)≤C*absNorm ν^(1/(k:ℝ)))
    (core ann minor : Set (CoordTorus K)) (hc : MeasurableSet core) (ha : MeasurableSet ann)
    (hm : MeasurableSet minor) (hdisj : Disjoint ann minor) (hcover : coreᶜ=ann∪minor)
    (Q δ A D P B H Dm : ℝ) (hQ : 0<Q) (hB : 0≤B) (hH : 0≤H)
    (hOrd : (∫ θ in ann, ‖fieldPowerSum k x w θ‖^(a+(m+d)) ∂latticeHaar) ≤ A*P*Q^(-δ))
    (hRest : (∫ θ, ‖fieldPowerSum k y v θ‖^(a+(m+d)) ∂latticeHaar)≤D*P)
    (hMin : ∀ θ∈minor, ‖fieldPowerSum k x w θ‖≤B)
    (hBox : ∀ θ∈minor, ‖fieldPowerSum k y v θ‖≤H)
    (hLow : (∫ θ, ‖fieldPowerSum k y v θ‖^m ∂latticeHaar)≤Dm)
    (hCore : (A+D)*P*Q^(-δ*a/((a:ℝ)+(m+d:ℕ)))+B^a*H^d*Dm <
      (∫ θ in core, (fieldPowerSum k x w θ)^a*(fieldPowerSum k y v θ)^(m+d)*
        conj (latticeCharacter (integerCoordinates K ν) θ) ∂latticeHaar).re) :
    PositiveRepresentation k (a+(m+d)) C ν := by
  apply positive_field_target_of_core k a (m+d) x y w v ν C hx hy hxb hyb core hc
  change (∫ θ in coreᶜ, ‖(fieldPowerSum k x w θ)^a*(fieldPowerSum k y v θ)^(m+d)*
    conj (latticeCharacter (integerCoordinates K ν) θ)‖ ∂latticeHaar) < _
  simp only [norm_mul,norm_pow,Complex.norm_conj,norm_latticeCharacter_eq_one,mul_one]
  have hFx := (continuous_frequencySum (fun i => integerCoordinates K ((x i)^k)) w).norm
  have hFy := (continuous_frequencySum (fun i => integerCoordinates K ((y i)^k)) v).norm
  have hi {f : CoordTorus K → ℝ} (hf : Continuous f) : Integrable f latticeHaar :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hInt : Integrable (fun θ => ‖fieldPowerSum k x w θ‖^a*‖fieldPowerSum k y v θ‖^(m+d))
      latticeHaar := hi ((hFx.pow _).mul (hFy.pow _))
  rw [hcover,setIntegral_union hdisj hm hInt.integrableOn hInt.integrableOn]
  apply lt_of_le_of_lt _ hCore
  apply add_le_add
  · exact annulus_pruning latticeHaar ann ha _ _ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      a (m+d) hS (hi (hFx.pow _)) (hi (hFy.pow _)) hInt Q δ A D P hQ hOrd hRest
  · exact outer_minor_bound latticeHaar minor hm _ _ (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) a m d B H Dm hB hH hMin hBox hInt (hi (hFy.pow _)) hLow

#print axioms positive_field_target_from_arc_estimates
end WaringLinear
