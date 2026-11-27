import WaringLinear.ConditionalGlobal
import WaringLinear.MarkedMinorAbsorption

/-! # Three-arc passage with the minor saving taken on marked roots -/
noncomputable section
open MeasureTheory WaringSiegel WaringSiegel.WSL2
open scoped NumberField BigOperators ComplexConjugate
namespace WaringLinear
variable {K : Type*} [Field K] [NumberField K]

structure MarkedBroadArcBounds (W : TraceSumFamily K) (k r a : ℕ) (ρ : ℝ) where
  major : ℕ → Set (ArchimedeanTraceTorus K)
  measurable : ∀ X, MeasurableSet (major X)
  A : ℝ
  B : ℝ
  C : ℝ
  B_nonneg : 0≤B
  C_nonneg : 0≤C
  ordinary : ∀ X : ℕ, 1≤X → ∀ q∈(major X)ᶜ, ‖W.ordinary k X q‖≤B*X
  marked : ∀ X : ℕ, 1≤X → ∀ q∈(major X)ᶜ, ‖W.restricted k X q‖≤C*(X:ℝ)^(1-ρ)
  moment : ∀ X : ℕ, 1≤X → (∫ q in major X, ‖W.ordinary k X q‖^(r+a) ∂traceHaar)≤A*(X:ℝ)^((r:ℝ)+a-k)

structure OneOrdinaryCore (W : TraceSumFamily K) (k r d X : ℕ) (ν : 𝓞 K)
    (Q C c A B H δ ρ : ℝ) where
  positive : ∀ i, W.point X i≠0 ∧ TotallyPositive (W.point X i)
  bounded : ∀ i, absNorm (W.point X i)≤C*absNorm ν^(1/(k:ℝ))
  core : Set (CoordTorus K)
  ann : Set (CoordTorus K)
  minor : Set (CoordTorus K)
  measCore : MeasurableSet core
  measAnn : MeasurableSet ann
  measMinor : MeasurableSet minor
  disjoint : Disjoint ann minor
  cover : coreᶜ=ann∪minor
  annulus : (∫ θ in ann, ‖fullCoordinate W k X θ‖^(1+(r+d)) ∂latticeHaar)≤A*(X:ℝ)^((r:ℝ)+d+1-k)*Q^(-δ)
  ordinary : ∀ θ∈minor, ‖fullCoordinate W k X θ‖≤B*X
  marked : ∀ θ∈minor, ‖markedCoordinate W k X θ‖≤H*(X:ℝ)^(1-ρ)
  mainTerm : c*(X:ℝ)^((r:ℝ)+d+1-k)≤(∫ θ in core, (fullCoordinate W k X θ)*
     (markedCoordinate W k X θ)^(r+d)*conj (latticeCharacter (integerCoordinates K ν) θ) ∂latticeHaar).re

def UniformOneOrdinaryCore (W : TraceSumFamily K) (k r d : ℕ) (ρ : ℝ) : Prop :=
  ∃ C c A B H δ : ℝ, 0<C ∧ 0<c ∧ 0≤B ∧ 0≤H ∧ 0<δ ∧
  ∀ Q : ℝ, 1≤Q → ∀ X₀ : ℝ, 1≤X₀ → ∃ N : ℝ, 0<N ∧
    ∀ ν : 𝓞 K, TotallyPositive ν → Eligible k ν → N<absNorm ν →
    ∃ X : ℕ, X₀≤(X:ℝ) ∧ Nonempty (OneOrdinaryCore W k r d X ν Q C c A B H δ ρ)

private theorem marked_outer_power (r d k : ℕ) (X B H D ρ ξ : ℝ) (hX : 0<X) :
    (B*X)*(H*X^(1-ρ))^d*(D*X^((r:ℝ)-k+ξ)) =
    X^((r:ℝ)+d+1-k)*(B*H^d*D*X^(-((d:ℝ)*ρ-ξ))) := by
  rw [mul_pow,←Real.rpow_natCast (X^(1-ρ)) d,←Real.rpow_mul hX.le]
  calc
    _ = (B*H^d*D)*((X^((1:ℝ)))*X^((1-ρ)*(d:ℝ))*X^((r:ℝ)-k+ξ)) := by rw [Real.rpow_one];ring
    _ = (B*H^d*D)*(X^((r:ℝ)+d+1-k)*X^(-((d:ℝ)*ρ-ξ))) := by
      rw [←Real.rpow_add hX,←Real.rpow_add hX,←Real.rpow_add hX]
      congr 2;ring
    _ = _ := by ring

/-- Only the marked roots have to save a power pointwise on the outer arcs.
The input at order r can have an epsilon loss, chosen after the strict gap. -/
theorem waring_siegel_of_marked_orders (W : ℝ → TraceSumFamily K) (k r a : ℕ) (x ρ : ℝ)
    (hk : k≠0) (ha : 0<a) (er : Even r) (ea : Even a)
    (moment : cutoffAdmissible W k r x) (gap : (k:ℝ)*x<((a:ℝ)-1)*ρ)
    (arcs : ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ →
      Nonempty (MarkedBroadArcBounds (W η) k r a ρ) ∧ UniformOneOrdinaryCore (W η) k r (a-1) ρ) :
    WaringSiegelBound K k (r+a) := by
  let d := a-1
  have hda : d+1=a := by unfold d;omega
  have hd : (d:ℝ)=(a:ℝ)-1 := by unfold d;rw [Nat.cast_sub (by omega : 1≤a),Nat.cast_one]
  let ε := (((d:ℝ)*ρ)-k*x)/2
  have he : 0<ε := by unfold ε;rw [hd];linarith
  have hh : 0<(d:ℝ)*ρ-(k*x+ε) := by unfold ε;rw [hd];linarith
  obtain ⟨η₁,h₁,low⟩ := moment ε he
  obtain ⟨η₂,h₂,high⟩ := cutoff_marked_loss_free_at W k r a x ρ er ea ha moment gap
  obtain ⟨η₃,h₃,arc⟩ := arcs
  let η := min η₁ (min η₂ η₃)
  have hη : 0<η := lt_min h₁ (lt_min h₂ h₃)
  obtain ⟨D,hD,lowM⟩ := low η hη (min_le_left _ _)
  obtain ⟨⟨broad⟩,C,c,A,B,H,δ,hC,hc,hB,hH,hδ,hcore⟩ :=
    arc η hη ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨E,highM⟩ := high η hη ((min_le_right _ _).trans (min_le_left _ _))
    broad.major broad.A broad.B broad.C broad.measurable broad.B_nonneg broad.C_nonneg
    broad.marked broad.ordinary broad.moment
  have hr : (0:ℝ)<1+(r+d:ℕ) := by positivity
  obtain ⟨Q,hQ,X₀,hX₀,error⟩ := choose_arc_parameters c (A+E) (B*H^d*D)
    (δ/(1+(r+d:ℕ))) ((d:ℝ)*ρ-(k*x+ε)) hc (div_pos hδ hr) hh
  obtain ⟨N,hN,core⟩ := hcore Q hQ X₀ hX₀
  refine ⟨C,hC,N,hN,?_⟩
  intro ν hν hνk hn
  obtain ⟨X,hx,⟨u⟩⟩ := core ν hν hνk hn
  have hx' : (0:ℝ)<X := zero_lt_one.trans_le (hX₀.trans hx)
  have hnat : 1≤X := by exact_mod_cast hX₀.trans hx
  let P := (X:ℝ)^((r:ℝ)+d+1-k)
  have hP : 0<P := Real.rpow_pos_of_pos hx' _
  have cost := mul_lt_mul_of_pos_right (error X hx) hP
  have hcost : (A+E)*P*Q^(-δ/(1+(r+d:ℕ)))+
      (B*X)*(H*(X:ℝ)^(1-ρ))^d*(D*(X:ℝ)^((r:ℝ)-k+(k*x+ε))) < c*P := by
    rw [marked_outer_power _ _ _ _ _ _ _ _ _ hx']
    change (A+E)*P*Q^(-δ/(1+(r+d:ℕ)))+P*(B*H^d*D*(X:ℝ)^(-((d:ℝ)*ρ-(k*x+ε))))<c*P
    rw [←neg_div] at cost
    linarith only [cost]
  have hS : 1+(r+d)=r+a := by omega
  have hS' : (r:ℝ)+d+1-k=(r:ℝ)+a-k := by rw [hd];ring
  have hhigh : (∫ θ, ‖markedCoordinate (W η) k X θ‖^(1+(r+d)) ∂latticeHaar)≤E*P := by
    rw [marked_coordinate_moment,hS]
    simpa only [P,hS'] using highM X hnat
  have hlow : (∫ θ, ‖markedCoordinate (W η) k X θ‖^r ∂latticeHaar)≤D*(X:ℝ)^((r:ℝ)-k+(k*x+ε)) := by
    rw [marked_coordinate_moment]
    simpa only [add_assoc] using lowM X hnat
  apply (positiveRepresentation_iff k _ hk C ν).1
  rw [←hS]
  apply positive_field_target_from_arc_estimates k 1 r d (by omega) ((W η).point X) ((W η).point X)
    (fun i => ((W η).full X i:ℂ)) (fun i => ((W η).small X i:ℂ)) ν C
    u.positive u.positive u.bounded u.bounded u.core u.ann u.minor u.measCore u.measAnn
    u.measMinor u.disjoint u.cover Q δ A E P (B*X) (H*(X:ℝ)^(1-ρ)) (D*(X:ℝ)^((r:ℝ)-k+(k*x+ε)))
    (zero_lt_one.trans_le hQ) (by positivity) (by positivity) u.annulus hhigh u.ordinary u.marked hlow
  simpa only [pow_one,Nat.cast_one,mul_one] using hcost.trans_le u.mainTerm

#print axioms waring_siegel_of_marked_orders
end WaringLinear
