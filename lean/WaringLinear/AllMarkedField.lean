import WaringLinear.FieldGlobal

/-! # The maximum of the local width and the global analytic threshold -/
noncomputable section
open MeasureTheory WaringSiegel WaringSiegel.WSL2 WaringEnvelope
open scoped NumberField BigOperators ComplexConjugate
namespace WaringLinear
variable {K : Type*} [Field K] [NumberField K]

/-- A single marked positive sum, the inner-core main term, the annular
error and the pointwise outer saving. Each actual norm and Haar integral
uses the specified support and target. -/
structure AllMarkedCore (W : TraceSumFamily K) (k s X : ℕ) (ν : 𝓞 K)
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
  annular : (∫ θ in ann, ‖markedCoordinate W k X θ‖^s ∂latticeHaar)≤A*(X:ℝ)^((s:ℝ)-k)*Q^(-δ)
  marked : ∀ θ∈minor, ‖markedCoordinate W k X θ‖≤B*(X:ℝ)^(1-ρ)
  box : ∀ θ∈minor, ‖markedCoordinate W k X θ‖≤H*X
  mainTerm : c*(X:ℝ)^((s:ℝ)-k)≤(∫ θ in core, (markedCoordinate W k X θ)^s*
    conj (latticeCharacter (integerCoordinates K ν) θ) ∂latticeHaar).re

def UniformAllMarkedCore (W : TraceSumFamily K) (k s : ℕ) (ρ : ℝ) : Prop :=
  ∃ C c A B H δ : ℝ, 0<C ∧ 0<c ∧ 0≤B ∧ 0≤H ∧ 0<δ ∧
  ∀ Q : ℝ, 1≤Q → ∀ X₀ : ℝ, 1≤X₀ → ∃ N : ℝ, 0<N ∧
    ∀ ν : 𝓞 K, TotallyPositive ν → Eligible k ν → N<absNorm ν →
    ∃ X : ℕ, X₀≤(X:ℝ) ∧ Nonempty (AllMarkedCore W k s X ν Q C c A B H δ ρ)

theorem all_marked_from_loss_free (W : TraceSumFamily K) (k S s : ℕ) (ρ E : ℝ)
    (hk : k≠0) (hs : S+1≤s) (hρ : 0<ρ)
    (moment : ∀ X : ℕ, 1≤X → (∫ q, ‖W.restricted k X q‖^S ∂traceHaar)≤E*(X:ℝ)^((S:ℝ)-k))
    (arc : UniformAllMarkedCore W k s ρ) : WaringSiegelBound K k s := by
  let d := s-S-1
  have hd : 1+(S+d)=s := by unfold d;omega
  have hd' : 1+(S:ℝ)+d=s := by exact_mod_cast (show 1+S+d=s by omega)
  obtain ⟨C,c,A,B,H,δ,hC,hc,hB,hH,hδ,hcore⟩ := arc
  obtain ⟨Q,hQ,X₀,hX₀,err⟩ := choose_arc_parameters c A (B*H^d*E) δ ρ hc hδ hρ
  obtain ⟨N,hN,has⟩ := hcore Q hQ X₀ hX₀
  refine ⟨C,hC,N,hN,?_⟩
  intro ν hν hνk hn
  obtain ⟨X,hx,⟨u⟩⟩ := has ν hν hνk hn
  have hX : 0<(X:ℝ) := zero_lt_one.trans_le (hX₀.trans hx)
  have hnat : 1≤X := by exact_mod_cast hX₀.trans hx
  let F (θ : CoordTorus K) : ℝ := ‖markedCoordinate W k X θ‖
  have hF : Continuous F := (continuous_frequencySum (fun i => integerCoordinates K ((W.point X i)^k))
    (fun i => (W.small X i:ℂ))).norm
  have hi {f : CoordTorus K → ℝ} (hf : Continuous f) : Integrable f latticeHaar :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hM : (∫ θ, F θ^S ∂latticeHaar)≤E*(X:ℝ)^((S:ℝ)-k) := by
    change (∫ θ, ‖markedCoordinate W k X θ‖^S ∂latticeHaar)≤_
    rw [marked_coordinate_moment]
    exact moment X hnat
  have hmin := outer_minor_bound latticeHaar u.minor u.measMinor F F (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    1 S d (B*(X:ℝ)^(1-ρ)) (H*X) (E*(X:ℝ)^((S:ℝ)-k))
    (by positivity) (by positivity) u.marked u.box
    (hi ((hF.pow 1).mul (hF.pow _))) (hi (hF.pow _)) hM
  have hpower (θ : CoordTorus K) : F θ * F θ^(S+d)=F θ^s := by
    calc
      _ = F θ^1 * F θ^(S+d) := by rw [pow_one]
      _ = _ := by rw [←pow_add,hd]
  simp only [pow_one,hpower] at hmin
  let P := (X:ℝ)^((s:ℝ)-k)
  have hprod : (B*(X:ℝ)^(1-ρ))*(H*X)^d*(E*(X:ℝ)^((S:ℝ)-k)) = B*H^d*E*(X:ℝ)^(-ρ)*P := by
    rw [mul_pow,←Real.rpow_natCast (X:ℝ) d]
    calc
      _ = B*H^d*E*((X:ℝ)^(1-ρ)*(X:ℝ)^(d:ℝ)*(X:ℝ)^((S:ℝ)-k)) := by ring
      _ = B*H^d*E*((X:ℝ)^(-ρ)*P) := by
        unfold P
        rw [←Real.rpow_add hX,←Real.rpow_add hX,←Real.rpow_add hX]
        congr 2
        linarith only [hd']
      _ = _ := by ring
  rw [hprod] at hmin
  have hscale := mul_lt_mul_of_pos_right (err X hx) (Real.rpow_pos_of_pos hX ((s:ℝ)-k))
  have hcost : A*P*Q^(-δ)+B*H^d*E*(X:ℝ)^(-ρ)*P<c*P := by
    dsimp only [P]
    linarith only [hscale]
  have hcomp : (∫ θ in u.coreᶜ, F θ^s ∂latticeHaar)<c*P := by
    rw [u.cover,setIntegral_union u.disjoint u.measMinor (hi (hF.pow s)).integrableOn (hi (hF.pow s)).integrableOn]
    exact (add_le_add u.annular hmin).trans_lt hcost
  apply (positiveRepresentation_iff k s hk C ν).1
  have hm := positive_field_target_of_core k s 0 (W.point X) (W.point X) (fun i => (W.small X i:ℂ))
    (fun i => (W.small X i:ℂ)) ν C u.positive u.positive u.bounded u.bounded u.core u.measCore
  apply hm
  change (∫ θ in u.coreᶜ, ‖(markedCoordinate W k X θ)^s*(markedCoordinate W k X θ)^0*
    conj (latticeCharacter (integerCoordinates K ν) θ)‖ ∂latticeHaar) < _
  simpa only [pow_zero,mul_one,norm_mul,norm_pow,Complex.norm_conj,norm_latticeCharacter_eq_one] using
    hcomp.trans_le u.mainTerm

/-- The local-width parameter enters only the uniform main-term and arc
hypotheses at the actual requested number of roots. -/
theorem field_max_width_linear_bound (W : ℝ → TraceSumFamily K) (k L : ℕ)
    (hk : 2501≤k) (count : DifferencingCounts W k)
    (shorten : ShorteningStep fieldConductorStage (cutoffAdmissible W k) k)
    (arcs : ∀ r a : ℕ, Even r → Even a → ((r+a+1:ℕ):ℝ)/k<6873/1000 →
      ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ →
        Nonempty (MarkedBroadArcBounds (W η) k r a (1/(15*k))) ∧
        UniformAllMarkedCore (W η) k (max L (r+a+1)) (1/(15*k))) :
    WaringSiegelBound K k (max L (6873*k/1000)) := by
  obtain ⟨r,a,er,ea,price,u,hu,e⟩ := field_marked_loss_free_of_differencing W k hk count shorten
  obtain ⟨v,hv,bounds⟩ := arcs r a er ea price
  let η := min u v
  have hη : 0<η := lt_min hu hv
  obtain ⟨⟨b⟩,core⟩ := bounds η hη (min_le_right _ _)
  obtain ⟨E,high⟩ := e η hη (min_le_left _ _) b.major b.A b.B b.C b.measurable
    b.B_nonneg b.C_nonneg b.marked b.ordinary b.moment
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hp := (div_lt_iff₀ hk').mp price
  have hpm : (r+a+1)*1000≤6873*k := by
    exact_mod_cast (show ((r+a+1:ℕ):ℝ)*1000≤6873*k by linarith only [hp])
  have hprice := (Nat.le_div_iff_mul_le (by decide : 0<1000)).2 hpm
  exact (all_marked_from_loss_free (W η) k (r+a) _ (1/(15*k)) E (by omega) (le_max_right _ _)
    (by positivity) (by simpa only [Nat.cast_add] using high) core).mono (max_le_max le_rfl hprice)

#print axioms all_marked_from_loss_free
#print axioms field_max_width_linear_bound
end WaringLinear
