import WaringEnvelope.DifferencingCells
import WaringEnvelope.RealCosts
import WaringEnvelope.ContinuousCover

/-! # Outward rounding at the dyadic conductor endpoints -/
noncomputable section
namespace WaringEnvelope

/-- The closed integer-grid inequalities of a dyadic row cover the entire
real interval between the two displayed endpoints. -/
theorem dyadic_integer_cell (j h v sig p q : ℕ) (u : ℝ) (hv : 0<v)
    (hbase : 2*(2^j*sig)≤T)
    (hstep : j=0 ∨ h*T≤v*(T-2^j*sig))
    (hleft : B*(j*h*T+2*(2^j*sig)*v) ≤ p*(T*v))
    (hright : q*T≤B*((j+2)*T-(4*(2^j*sig)-2*sig)))
    (hul : (p:ℝ)/B≤u) (huu : u≤(q:ℝ)/B) :
    DifferencingBranch ((h:ℝ)/v) j u ((sig:ℝ)/T) := by
  have hT : (0:ℝ)<T := by norm_num [T]
  have hB : (0:ℝ)<B := by norm_num [B]
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have hpow : 1≤2^j := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  have hys : sig≤2^j*sig := by simpa using Nat.mul_le_mul_right sig hpow
  have hsub1 : 2*sig≤4*(2^j*sig) := by omega
  have hjT : 2*T≤(j+2)*T := Nat.mul_le_mul_right T (by omega)
  have hsub2 : 4*(2^j*sig)-2*sig≤(j+2)*T := by omega
  have hsub3 : 2^j*sig ≤ T := by omega
  apply interval_has_differencing_branch _ _ _ _ (by positivity) (by positivity)
  · have h' : (2:ℝ)*(2^j*(sig:ℝ)) ≤ T := by exact_mod_cast hbase
    field_simp
    linarith
  · rcases hstep with h0|h0
    · exact Or.inl h0
    · right
      have hh : (h:ℝ)*T ≤ v*((T:ℝ)-2^j*sig) := by
        exact_mod_cast (show h*T≤v*(T-2^j*sig) from h0)
      field_simp
      linarith
  · apply le_trans _ hul
    have hh : (B:ℝ)*(j*h*T+2*(2^j*(sig:ℝ))*v) ≤ p*(T*v) := by exact_mod_cast hleft
    unfold diffLower
    field_simp
    linarith
  · apply huu.trans
    have hh : (q:ℝ)*T ≤ B*((j+2)*T-(4*(2^j*(sig:ℝ))-2*sig)) := by
      exact_mod_cast hright
    unfold diffUpper
    field_simp
    linarith

end WaringEnvelope
