import WaringEnvelope.WeylCells
import WaringEnvelope.RealCosts

/-! # Integer-grid endpoints of the finite Weyl cells -/
noncomputable section
namespace WaringEnvelope

theorem weyl_integer_cell (j K h v sig p q : ℕ) (u : ℝ) (hv : 0<v)
    (hj : 2≤j) (hK : j≤K) (hq : 0<q)
    (hleft : B*(j+1)*(weylWeight j*sig*v+j*h*T) ≤ p*(T*v))
    (hright : q*(T*v) ≤ B*min
      ((j+1)*(T*v-h*T-weylWeight j*sig*v))
      (j*(T*v)-j*h*T-weylWeight j*sig*v))
    (hul : (p:ℝ)/B≤u) (huu : u≤(q:ℝ)/B) :
    WeylBranch K ((h:ℝ)/v) u ((sig:ℝ)/T) := by
  have hTn : 0<T := by decide
  have hT : (0:ℝ)<T := by exact_mod_cast hTn
  have hB : (0:ℝ)<B := by norm_num [B]
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have hp : 0<q*(T*v) := Nat.mul_pos hq (Nat.mul_pos hTn hv)
  have h1 := hright.trans (Nat.mul_le_mul_left B (Nat.min_le_left _ _))
  have h2 := hright.trans (Nat.mul_le_mul_left B (Nat.min_le_right _ _))
  have h1' : h*T+weylWeight j*sig*v≤T*v := by
    by_contra! ht
    have hz : T*v-h*T-weylWeight j*sig*v=0 := by omega
    rw [hz,Nat.mul_zero,Nat.mul_zero] at h1
    omega
  have h2' : j*h*T+weylWeight j*sig*v≤j*(T*v) := by
    by_contra! ht
    have hz : j*(T*v)-j*h*T-weylWeight j*sig*v=0 := by omega
    rw [hz,Nat.mul_zero] at h2
    omega
  have hL : (B:ℝ)*(j+1)*(weylWeight j*(sig:ℝ)*v+j*h*T) ≤ p*(T*v) := by exact_mod_cast hleft
  have h1raw : ((q*(T*v):ℕ):ℝ) ≤ (B*((j+1)*(T*v-h*T-weylWeight j*sig*v)):ℕ) := by
    exact_mod_cast h1
  have h2raw : ((q*(T*v):ℕ):ℝ) ≤ (B*(j*(T*v)-j*h*T-weylWeight j*sig*v):ℕ) := by
    exact_mod_cast h2
  push_cast [Nat.cast_sub (show weylWeight j*sig*v ≤ T*v-h*T by omega),
    Nat.cast_sub (show h*T≤T*v by omega)] at h1raw
  push_cast [Nat.cast_sub (show weylWeight j*sig*v ≤ j*(T*v)-j*h*T by omega),
    Nat.cast_sub (show j*h*T≤j*(T*v) by omega)] at h2raw
  refine ⟨j,hj,hK,(weylAt_iff_endpoints _ _ _ _).2 ⟨?_,?_⟩⟩
  · apply le_trans _ hul
    unfold weylLower
    field_simp
    linarith only [hL]
  · apply huu.trans
    apply le_min
    · field_simp
      linarith only [h1raw]
    · field_simp
      linarith only [h2raw]

end WaringEnvelope
