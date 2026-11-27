import WaringLinear.LocalWidthGlobal

/-! # From a sharp marked moment to a locally conditioned representation bound -/
noncomputable section
open WaringSiegel WaringSiegel.WSL2 WaringEnvelope
namespace WaringLinear
variable {K : Type*} [Field K] [NumberField K]

def LocalizedMarkedArcs (W : ℝ → TraceSumFamily K) (k L : ℕ) : Prop :=
  ∀ r a : ℕ, Even r → Even a → ((r+a+1:ℕ):ℝ)/k<6873/1000 →
    ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ →
      Nonempty (MarkedBroadArcBounds (W η) k r a (1/(15*k))) ∧
      LocalAllMarkedCore (W η) k (max L (r+a+1)) (1/(15*k))

theorem max_width_from_marked_moment (W : ℝ → TraceSumFamily K) (k L : ℕ) (hk : 0<k)
    (width : PrimitiveWidthBound K k L)
    (order : ∃ r a : ℕ, Even r ∧ Even a ∧ ((r+a+1:ℕ):ℝ)/k<6873/1000 ∧
      ∃ u : ℝ, 0<u ∧ ∀ η : ℝ, 0<η → η≤u → uniformMarkedMomentAt (W η) k r a (1/(15*k)))
    (arcs : LocalizedMarkedArcs W k L) : WaringSiegelBound K k (max L (6873*k/1000)) := by
  obtain ⟨r,a,er,ea,price,u,hu,e⟩ := order
  obtain ⟨v,hv,bounds⟩ := arcs r a er ea price
  let η := min u v
  have hη : 0<η := lt_min hu hv
  obtain ⟨⟨b⟩,localCore⟩ := bounds η hη (min_le_right _ _)
  have core := UniformAllMarkedCore.of_width localCore hk (le_max_left _ _) width
  obtain ⟨E,high⟩ := e η hη (min_le_left _ _) b.major b.A b.B b.C b.measurable
    b.B_nonneg b.C_nonneg b.marked b.ordinary b.moment
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have hp := (div_lt_iff₀ hk').mp price
  have hpm : (r+a+1)*1000≤6873*k := by
    exact_mod_cast (show ((r+a+1:ℕ):ℝ)*1000≤6873*k by linarith only [hp])
  have hprice := (Nat.le_div_iff_mul_le (by decide : 0<1000)).2 hpm
  exact (all_marked_from_loss_free (W η) k (r+a) _ (1/(15*k)) E hk.ne' (le_max_right _ _)
    (by positivity) (by simpa only [Nat.cast_add] using high) core).mono (max_le_max le_rfl hprice)

#print axioms max_width_from_marked_moment
end WaringLinear
