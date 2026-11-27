import WaringLinear.AsymptoticArcs
import WaringLinear.SharpTraceMoments

/-! # The sharp schedule and the actual global representation predicate

All unproved analytic inputs are exposed. In particular, the lower
bound on the mixed core is uniform over the eligible targets under
consideration. The moment and error comparisons are derived inside
the theorem.
-/
noncomputable section
open MeasureTheory WaringSiegel WaringSiegel.WSL2 WaringEnvelope WaringDualEnvelope
open scoped NumberField BigOperators ComplexConjugate
namespace WaringLinear
variable {K : Type*} [Field K] [NumberField K]

structure OrdinaryArcBounds (W : TraceSumFamily K) (k r a : ℕ) where
  major : ℕ → Set (ArchimedeanTraceTorus K)
  measurable : ∀ X, MeasurableSet (major X)
  A : ℝ
  B : ℝ
  C : ℝ
  B_nonneg : 0≤B
  C_nonneg : 0≤C
  boxBound : ∀ X : ℕ, 1≤X → ∀ q∈(major X)ᶜ, ‖W.restricted k X q‖≤C*X
  minorBound : ∀ X : ℕ, 1≤X → ∀ q∈(major X)ᶜ, ‖W.ordinary k X q‖≤B*(X:ℝ)^(1-TraceSumFamily.minorSaving k)
  majorBound : ∀ X : ℕ, 1≤X → (∫ q in major X, ‖W.ordinary k X q‖^(r+a) ∂traceHaar)≤A*(X:ℝ)^((r:ℝ)+a-k)

def fullCoordinate (W : TraceSumFamily K) (k X : ℕ) :=
  fieldPowerSum k (W.point X) (fun i => (W.full X i:ℂ))
def markedCoordinate (W : TraceSumFamily K) (k X : ℕ) :=
  fieldPowerSum k (W.point X) (fun i => (W.small X i:ℂ))

structure MixedCoreBounds (W : TraceSumFamily K) (k r a X : ℕ) (ν : 𝓞 K) (Q C c A B δ : ℝ) where
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
  annulus : (∫ θ in ann, ‖fullCoordinate W k X θ‖^(a+r) ∂latticeHaar)≤A*(X:ℝ)^((a:ℝ)+r-k)*Q^(-δ)
  outer : ∀ θ∈minor, ‖fullCoordinate W k X θ‖≤B*(X:ℝ)^(1-TraceSumFamily.minorSaving k)
  mainTerm : c*(X:ℝ)^((a:ℝ)+r-k)≤(∫ θ in core, (fullCoordinate W k X θ)^a*
    (markedCoordinate W k X θ)^r*conj (latticeCharacter (integerCoordinates K ν) θ) ∂latticeHaar).re

def UniformCore (W : TraceSumFamily K) (k r a : ℕ) : Prop :=
  ∃ C c A B δ : ℝ, 0<C ∧ 0<c ∧ 0≤B ∧ 0<δ ∧
    ∀ Q : ℝ, 1≤Q → ∀ X₀ : ℝ, 1≤X₀ → ∃ N : ℝ, 0<N ∧
      ∀ ν : 𝓞 K, TotallyPositive ν → Eligible k ν → N<absNorm ν →
      ∃ X : ℕ, X₀≤(X:ℝ) ∧ Nonempty (MixedCoreBounds W k r a X ν Q C c A B δ)

theorem marked_coordinate_moment (W : TraceSumFamily K) (k X p : ℕ) :
    (∫ θ, ‖markedCoordinate W k X θ‖^p ∂latticeHaar)=
      ∫ q, ‖W.restricted k X q‖^p ∂traceHaar :=
  (traceWeylSum_integral_norm_pow k p (W.point X) (fun i => (W.small X i:ℂ))).symm

theorem sharp_waring_siegel_of_analytic_inputs (W : ℝ → TraceSumFamily K) (k : ℕ) (hk : 21≤k)
    (seed : SelectedSeeds (cutoffAdmissible W k) k)
    (finiteStep : k<180000^2 → ShorteningStep DualStage (cutoffAdmissible W k) k)
    (largeStep : 180000^2≤k → ShorteningStep WaringSharpTail.Branch (cutoffAdmissible W k) k)
    (arcs : ∀ r a : ℕ, Even r → Even a → 0<a → ((r+a+1:ℕ):ℝ)/k<6873/1000 →
      ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ →
        Nonempty (OrdinaryArcBounds (W η) k r a) ∧ UniformCore (W η) k r a) :
    ∃ s : ℕ, ((s+1:ℕ):ℝ)/k<6873/1000 ∧ WaringSiegelBound K k s := by
  obtain ⟨r,a,x,er,ea,hm,hx,gap,price⟩ :=
    WaringSharp.all_shortening_orders_with_extra_6873 k hk _ seed finiteStep largeStep
  let ρ := TraceSumFamily.minorSaving k
  have hg : (k:ℝ)*x<(a:ℝ)*ρ := by simpa [ρ,TraceSumFamily.minorSaving,div_eq_mul_inv] using gap
  have ha : 0<a := by
    by_contra! hh
    have he : a=0 := Nat.eq_zero_of_le_zero hh
    simp [he] at hg
    exact (not_lt_of_ge (mul_nonneg (Nat.cast_nonneg k) hx)) hg
  let ε := ((a:ℝ)*ρ-k*x)/2
  have hε : 0<ε := by unfold ε;linarith
  obtain ⟨η₁,h₁,low⟩ := hm ε hε
  obtain ⟨η₂,h₂,high⟩ := cutoff_loss_free_at W k r a x er ea hm hx gap
  obtain ⟨η₃,h₃,ordinary⟩ := arcs r a er ea ha price
  let η := min η₁ (min η₂ η₃)
  have hη : 0<η := lt_min h₁ (lt_min h₂ h₃)
  obtain ⟨D,hD,lowM⟩ := low η hη (min_le_left _ _)
  obtain ⟨⟨broad⟩,C,c,A,B,δ,hC,hc,hB,hδ,hcore⟩ :=
    ordinary η hη ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨E,highM⟩ := high η hη ((min_le_right _ _).trans (min_le_left _ _))
    broad.major broad.A broad.B broad.C broad.measurable broad.B_nonneg broad.C_nonneg
    broad.boxBound broad.minorBound broad.majorBound
  refine ⟨a+r,by simpa only [Nat.add_comm a r] using price,?_⟩
  apply waring_siegel_of_arc_estimates k a r C c A E B D δ ρ (k*x+ε)
    (by omega) ha hC hc hB hδ (by unfold ε;linarith)
  intro Q hQ X₀ hX₀
  obtain ⟨N,hN,hN'⟩ := hcore Q hQ X₀ hX₀
  refine ⟨N,hN,?_⟩
  intro ν hp he hn
  obtain ⟨X,hX,⟨u⟩⟩ := hN' ν hp he hn
  have hnat : 1≤X := by exact_mod_cast hX₀.trans hX
  refine ⟨X,hX,⟨{
    nx := (W η).count X
    ny := (W η).count X
    x := (W η).point X
    y := (W η).point X
    w := fun i => ((W η).full X i:ℂ)
    v := fun i => ((W η).small X i:ℂ)
    xpositive := u.positive
    ypositive := u.positive
    xbound := u.bounded
    ybound := u.bounded
    core := u.core
    ann := u.ann
    minor := u.minor
    measCore := u.measCore
    measAnn := u.measAnn
    measMinor := u.measMinor
    disjoint := u.disjoint
    cover := u.cover
    ordinaryAnn := u.annulus
    minorOrdinary := u.outer
    positiveCore := u.mainTerm
    fullRestricted := ?_
    lowRestricted := ?_
  }⟩⟩
  · change (∫ θ, ‖markedCoordinate (W η) k X θ‖^(a+r) ∂latticeHaar)≤_
    rw [marked_coordinate_moment]
    simpa only [Nat.add_comm r a,add_comm (r:ℝ) a] using highM X hnat
  · change (∫ θ, ‖markedCoordinate (W η) k X θ‖^r ∂latticeHaar)≤_
    rw [marked_coordinate_moment]
    simpa only [add_assoc] using lowM X hnat

#print axioms sharp_waring_siegel_of_analytic_inputs
end WaringLinear
