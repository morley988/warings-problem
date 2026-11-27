import WaringLinear.ThreeArcEndgame
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform three-arc bounds imply eventual positive representations -/
noncomputable section
open MeasureTheory Filter WaringSiegel WaringSiegel.WSL2
open scoped NumberField BigOperators ComplexConjugate Topology
namespace WaringLinear

theorem choose_arc_parameters (c H B t d : ℝ) (hc : 0<c) (ht : 0<t) (hd : 0<d) :
    ∃ Q : ℝ, 1≤Q ∧ ∃ X₀ : ℝ, 1≤X₀ ∧ ∀ X : ℝ, X₀≤X →
      H*Q^(-t)+B*X^(-d)<c := by
  have hQ : Tendsto (fun Q : ℝ => H*Q^(-t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=H)).mul (tendsto_rpow_neg_atTop ht)
  have hX : Tendsto (fun X : ℝ => B*X^(-d)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=B)).mul (tendsto_rpow_neg_atTop hd)
  obtain ⟨Q,hQ₁,hQ₂⟩ := ((eventually_ge_atTop (1:ℝ)).and (hQ.eventually_lt_const (half_pos hc))).exists
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.1 (hX.eventually_lt_const (half_pos hc))
  refine ⟨Q,hQ₁,max 1 X₀,le_max_left _ _,?_⟩
  intro X h
  have hX₂ := hX₀ X ((le_max_right _ _).trans h)
  linarith

variable {K : Type*} [Field K] [NumberField K]

/-- Ordinary and restricted supports on the actual coordinate torus. The
core has a positive main term. The annular ordinary moment decays in Q
and the pointwise outer minor arcs save rho. -/
structure FieldArcEstimates (k a r : ℕ) (ν : 𝓞 K) (X Q C c A E B D δ ρ ξ : ℝ) where
  nx : ℕ
  ny : ℕ
  x : Fin nx → 𝓞 K
  y : Fin ny → 𝓞 K
  w : Fin nx → ℂ
  v : Fin ny → ℂ
  xpositive : ∀ i, x i≠0 ∧ TotallyPositive (x i)
  ypositive : ∀ i, y i≠0 ∧ TotallyPositive (y i)
  xbound : ∀ i, absNorm (x i)≤C*absNorm ν^(1/(k:ℝ))
  ybound : ∀ i, absNorm (y i)≤C*absNorm ν^(1/(k:ℝ))
  core : Set (CoordTorus K)
  ann : Set (CoordTorus K)
  minor : Set (CoordTorus K)
  measCore : MeasurableSet core
  measAnn : MeasurableSet ann
  measMinor : MeasurableSet minor
  disjoint : Disjoint ann minor
  cover : coreᶜ=ann∪minor
  ordinaryAnn : (∫ θ in ann, ‖fieldPowerSum k x w θ‖^(a+r) ∂latticeHaar)≤
    A*X^((a:ℝ)+r-k)*Q^(-δ)
  fullRestricted : (∫ θ, ‖fieldPowerSum k y v θ‖^(a+r) ∂latticeHaar)≤E*X^((a:ℝ)+r-k)
  minorOrdinary : ∀ θ∈minor, ‖fieldPowerSum k x w θ‖≤B*X^(1-ρ)
  lowRestricted : (∫ θ, ‖fieldPowerSum k y v θ‖^r ∂latticeHaar)≤D*X^((r:ℝ)-k+ξ)
  positiveCore : c*X^((a:ℝ)+r-k)≤(∫ θ in core, (fieldPowerSum k x w θ)^a*
    (fieldPowerSum k y v θ)^r*conj (latticeCharacter (integerCoordinates K ν) θ) ∂latticeHaar).re

theorem outer_cost_power (a r k : ℕ) (X B D ρ ξ : ℝ) (hX : 0<X) :
    (B*X^(1-ρ))^a*(D*X^((r:ℝ)-k+ξ))=
    X^((a:ℝ)+r-k)*(B^a*D*X^(-((a:ℝ)*ρ-ξ))) := by
  rw [mul_pow,←Real.rpow_natCast (X^(1-ρ)) a,←Real.rpow_mul hX.le]
  calc
    _ = B^a*D*(X^(((1-ρ)*(a:ℝ)))*X^((r:ℝ)-k+ξ)) := by ring
    _ = B^a*D*(X^((a:ℝ)+r-k)*X^(-((a:ℝ)*ρ-ξ))) := by
      rw [←Real.rpow_add hX,←Real.rpow_add hX]
      congr 2 <;> ring
    _ = _ := by ring

/-- Quantified arc estimates produce the literal global Waring–Siegel
predicate with the given number of variables. The scale may depend on the
target algebraic integer and the chosen fixed core width. -/
theorem waring_siegel_of_arc_estimates (k a r : ℕ) (C c A E B D δ ρ ξ : ℝ)
    (hk : k≠0) (ha : 0<a) (hC : 0<C) (hc : 0<c) (hB : 0≤B) (hδ : 0<δ)
    (gap : ξ<(a:ℝ)*ρ)
    (arcs : ∀ Q : ℝ, 1≤Q → ∀ X₀ : ℝ, 1≤X₀ → ∃ N : ℝ, 0<N ∧
      ∀ ν : 𝓞 K, TotallyPositive ν → Eligible k ν → N<absNorm ν →
      ∃ X : ℝ, X₀≤X ∧ Nonempty (FieldArcEstimates k a r ν X Q C c A E B D δ ρ ξ)) :
    WaringSiegelBound K k (a+r) := by
  have ha' : 0<(a:ℝ) := by exact_mod_cast ha
  have hs : 0<(a:ℝ)+r := by positivity
  obtain ⟨Q,hQ,X₀,hX₀,herr⟩ := choose_arc_parameters c (A+E) (B^a*D)
    (δ*a/(a+r:ℝ)) ((a:ℝ)*ρ-ξ) hc (div_pos (mul_pos hδ ha') hs) (sub_pos.mpr gap)
  obtain ⟨N,hN,H⟩ := arcs Q hQ X₀ hX₀
  refine ⟨C,hC,N,hN,?_⟩
  intro ν hν hνk hnorm
  obtain ⟨X,hscale,⟨data⟩⟩ := H ν hν hνk hnorm
  have hX := zero_lt_one.trans_le (hX₀.trans hscale)
  have Hbox : ∀ θ∈data.minor, ‖fieldPowerSum k data.y data.v θ‖≤∑ i, ‖data.v i‖ := by
    intro θ _
    unfold fieldPowerSum frequencySum
    exact (norm_sum_le _ _).trans_eq (by simp [norm_latticeCharacter_eq_one])
  have hpos := Real.rpow_pos_of_pos hX ((a:ℝ)+r-k)
  have hraw := mul_lt_mul_of_pos_right (herr X hscale) hpos
  have hcost : (A+E)*X^((a:ℝ)+r-k)*Q^(-δ*a/((a:ℝ)+r))+
      (B*X^(1-ρ))^a*(D*X^((r:ℝ)-k+ξ)) < c*X^((a:ℝ)+r-k) := by
    rw [outer_cost_power _ _ _ _ _ _ _ _ hX]
    rw [show -(δ*(a:ℝ)/((a:ℝ)+r))=(-δ)*(a:ℝ)/((a:ℝ)+r) by ring] at hraw
    linarith only [hraw]
  apply (positiveRepresentation_iff k (a+r) hk C ν).1
  have hRep := positive_field_target_from_arc_estimates k a r 0 (by omega) data.x data.y data.w data.v
    ν C data.xpositive data.ypositive data.xbound data.ybound data.core data.ann data.minor data.measCore
    data.measAnn data.measMinor data.disjoint data.cover Q δ A E (X^((a:ℝ)+r-k))
    (B*X^(1-ρ)) (∑ i, ‖data.v i‖) (D*X^((r:ℝ)-k+ξ)) (zero_lt_one.trans_le hQ)
    (mul_nonneg hB (Real.rpow_nonneg hX.le _)) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (by simpa using data.ordinaryAnn) (by simpa using data.fullRestricted) data.minorOrdinary Hbox
    data.lowRestricted (by simpa using hcost.trans_le data.positiveCore)
  simpa using hRep

#print axioms waring_siegel_of_arc_estimates
end WaringLinear
