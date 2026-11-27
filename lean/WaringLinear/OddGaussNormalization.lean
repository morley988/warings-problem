import WaringLinear.QuadraticGauss

/-! # The common quadratic phase at odd conductors

The exact radical formula normalizes a pure complete sum independently of
linear or constant twists. Its normalization has unit complex norm.
-/
noncomputable section
namespace WaringLinear
open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [Fintype A]

/-- The cardinality of the additive kernel of multiplication by `d`. -/
def annCard (d : A) : ℕ := (Finset.univ.filter (fun t : A => d*t=0)).card

theorem annCard_pos (d : A) : 0 < annCard d := by
  apply Finset.card_pos.mpr
  exact ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,mul_zero _⟩⟩

/-- The magnitude of a quadratic sum over a square step equals the kernel
cardinality times the square root of the whole ring cardinality. -/
theorem norm_oddGauss (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive) (h d : A)
    (hh : IsUnit (2*h)) (hcard : annCard (d^2)=(annCard d)^2) :
    ‖∑ t : A, ψ ((h*d^2)*t^2)‖ = (annCard d : ℝ)*Real.sqrt (Fintype.card A : ℝ) := by
  classical
  have hker (t : A) : 2*(h*d^2)*t=0 ↔ d^2*t=0 := by
    rw [show 2*(h*d^2)*t=(2*h)*(d^2*t) by ring]
    simpa only [mul_zero] using hh.mul_right_inj (b := d^2*t) (c := 0)
  have hphase (t : A) (ht : 2*(h*d^2)*t=0) : ψ ((h*d^2)*t^2+0*t)=1 := by
    rw [show (h*d^2)*t^2+0*t=h*t*(d^2*t) by ring,(hker t).mp ht,mul_zero,ψ.map_zero_eq_one]
  have hz := norm_quadraticGauss_of_radical_trivial ψ hψ (h*d^2) 0 0 hphase
  simp only [zero_mul,add_zero,hker] at hz
  change ‖∑ t : A, ψ ((h*d^2)*t^2)‖ = Real.sqrt ((Fintype.card A : ℝ)*(annCard (d^2) : ℝ)) at hz
  rw [hz,hcard,Nat.cast_pow,Real.sqrt_mul (by positivity),Real.sqrt_sq (by positivity),mul_comm]

/-- The normalized, untwisted phase at the fixed Hessian and step. -/
def oddGaussPhase (ψ : AddChar A ℂ) (h d : A) : ℂ :=
  (∑ t : A, ψ ((h*d^2)*t^2)) / (((annCard d : ℝ)*Real.sqrt (Fintype.card A : ℝ) : ℝ) : ℂ)

theorem norm_oddGaussPhase (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive) (h d : A)
    (hh : IsUnit (2*h)) (hcard : annCard (d^2)=(annCard d)^2) :
    ‖oddGaussPhase ψ h d‖=1 := by
  have hd : (0:ℝ)<annCard d := by exact_mod_cast annCard_pos d
  have hA : (0:ℝ)<Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hM : 0<(annCard d:ℝ)*Real.sqrt (Fintype.card A : ℝ) := by positivity
  rw [oddGaussPhase,norm_div,norm_oddGauss ψ hψ h d hh hcard,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hM,div_self hM.ne']

/-- Every twist admitting a stationary point has the same canonical phase
`oddGaussPhase ψ h d`, multiplied by the character at that point. -/
theorem oddGauss_common_phase (ψ : AddChar A ℂ) (h d b c x₀ : A)
    (hx : 2*(h*d^2)*x₀+b=0) :
    (∑ t : A, ψ ((h*d^2)*t^2+b*t+c)) =
      ψ ((h*d^2)*x₀^2+b*x₀+c)*oddGaussPhase ψ h d*
        (((annCard d:ℝ)*Real.sqrt (Fintype.card A:ℝ):ℝ):ℂ) := by
  have hd : (0:ℝ)<annCard d := by exact_mod_cast annCard_pos d
  have hA : (0:ℝ)<Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hM : (0:ℝ)<(annCard d:ℝ)*Real.sqrt (Fintype.card A:ℝ) := by positivity
  have hMc : (((annCard d:ℝ)*Real.sqrt (Fintype.card A:ℝ):ℝ):ℂ)≠0 := by exact_mod_cast hM.ne'
  rw [quadraticGauss_stationary_phase ψ (h*d^2) b c x₀ hx,oddGaussPhase]
  field_simp

#print axioms norm_oddGauss
#print axioms norm_oddGaussPhase
#print axioms oddGauss_common_phase
end WaringLinear
