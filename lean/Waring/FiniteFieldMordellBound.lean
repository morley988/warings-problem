import Waring.FiniteFieldMordellAffine
import Waring.EndgameCompletionCompleteSums

/-! # Mordell cancellation for a general complete polynomial sum

The full coefficient moment and the affine orbit are both literal finite
objects. This proves the degree-dependent p^(1-1/d) saving without a Weil
bound. The larger harmless constant comes from the d^d Newton fiber bound.
-/

noncomputable section
open Polynomial
open scoped BigOperators Polynomial
namespace Waring.FiniteFieldMordell

def polynomialSum (q : ℕ) [NeZero q] (f : (ZMod q)[X]) : ℂ :=
  ∑ x : ZMod q,ZMod.stdAddChar (f.eval x)

theorem coefficientSum_eq_polynomialSum {q d : ℕ} [NeZero q] (f : (ZMod q)[X])
    (hd : f.natDegree ≤ d) (hzero : f.coeff 0=0) :
    coefficientSum q d (fun j => f.coeff (j.val+1))=polynomialSum q f := by
  unfold coefficientSum polynomialSum
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [eval_eq_sum_range' (show f.natDegree<d+1 by omega) x,Finset.sum_range_succ']
  simp only [hzero,zero_mul,add_zero]
  simpa only using (Fin.sum_univ_eq_sum_range (fun j => f.coeff (j+1)*x^(j+1)) d)

theorem polynomialSum_affine_norm {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)[X]) {u : ZMod p} (hu : u ≠ 0) (v : ZMod p) :
    ‖polynomialSum p (affinePolynomial f u v)‖=‖polynomialSum p f‖ := by
  have hshift : (∑ x : ZMod p,ZMod.stdAddChar (f.eval (u*x+v)))=
      ∑ x : ZMod p,ZMod.stdAddChar (f.eval x) := by
    apply Fintype.sum_equiv ((Equiv.mulLeft₀ u hu).trans (Equiv.addRight v))
    intro x
    rfl
  unfold polynomialSum
  simp only [affinePolynomial,eval_comp,eval_add,eval_mul,eval_C,eval_X,eval_neg,
    sub_eq_add_neg,AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul,norm_mul,hshift]
  simp [ZMod.stdAddChar_apply]

theorem coefficientSum_affine_norm {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)[X]) (u : (ZMod p)ˣ) (v : ZMod p) :
    ‖coefficientSum p f.natDegree (affineCoefficients f f.natDegree u v)‖=
      ‖polynomialSum p f‖ := by
  rw [show affineCoefficients f f.natDegree u v=
    (fun j : Fin f.natDegree => (affinePolynomial f u v).coeff (j.val+1)) from rfl,
    coefficientSum_eq_polynomialSum _ (affinePolynomial_natDegree f u.ne_zero v).le
      (affinePolynomial_coeff_zero f u v),polynomialSum_affine_norm f u.ne_zero v]

theorem affineCoefficients_fiber_card_le {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)[X]) (hf : 2 ≤ f.natDegree) (hfp : f.natDegree<p)
    (a : Fin f.natDegree → ZMod p) :
    (Finset.univ.filter (fun z : (ZMod p)ˣ × ZMod p =>
      affineCoefficients f f.natDegree z.1 z.2=a)).card ≤ f.natDegree := by
  have hd : 1 ≤ f.natDegree := by omega
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr
    (ne_zero_of_natDegree_gt (show 0<f.natDegree by omega))
  have hchar : (f.natDegree : ZMod p) ≠ 0 := by
    intro hz
    have hdiv := (ZMod.natCast_eq_zero_iff f.natDegree p).mp hz
    have hh := Nat.le_of_dvd (show 0<f.natDegree by omega) hdiv
    omega
  let last : Fin f.natDegree := ⟨f.natDegree-1,by omega⟩
  apply le_trans (Finset.card_le_card_of_injOn
    (fun z : (ZMod p)ˣ × ZMod p => (z.1 : ZMod p))
    (t := Finset.univ.filter (fun u : ZMod p => u^f.natDegree=a last/f.leadingCoeff)) ?_ ?_)
    (EndgameCompletion.card_pow_fiber_le f.natDegree (by omega) _)
  · intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(eq_div_iff hlc).mpr ?_⟩
    have he := congrFun (Finset.mem_filter.mp hz).2 last
    simp only [affineCoefficients,last,Nat.sub_add_cancel hd,affinePolynomial_coeff_top f hd] at he
    simpa only [mul_comm] using he
  · rintro ⟨u,v⟩ hx ⟨w,z⟩ hy hu
    have huw : u=w := Units.ext hu
    subst w
    have he := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have hvz := affineCoefficients_translation_injective f hf hchar u.ne_zero he
    exact Prod.ext rfl hvz

/-- The actual complete polynomial sum has the Mordell exponent. All
coefficients are arbitrary, including the linear and constant terms. -/
theorem polynomialSum_mordell_power {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)[X]) (hf : 2 ≤ f.natDegree) (hfp : f.natDegree<p) :
    ‖polynomialSum p f‖^(2*f.natDegree) ≤
      2*(f.natDegree : ℝ)^(f.natDegree+1)*(p : ℝ)^(2*f.natDegree-2) := by
  let d := f.natDegree
  have hweighted := EndgameCompletion.sum_comp_le_fiber_bound
    (Finset.univ : Finset ((ZMod p)ˣ × ZMod p))
    (fun z => affineCoefficients f d z.1 z.2)
    (fun a => ‖coefficientSum p d a‖^(2*d)) d
    (fun _ => by positivity) (affineCoefficients_fiber_card_le f hf hfp)
  have hleft : (∑ z : (ZMod p)ˣ × ZMod p,
      ‖coefficientSum p d (affineCoefficients f d z.1 z.2)‖^(2*d))=
      ((p : ℝ)-1)*(p : ℝ)*‖polynomialSum p f‖^(2*d) := by
    change (∑ z : (ZMod p)ˣ × ZMod p, ‖coefficientSum p f.natDegree
      (affineCoefficients f f.natDegree z.1 z.2)‖^(2*d)) = _
    simp_rw [coefficientSum_affine_norm]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,ZMod.card_units,ZMod.card,
      nsmul_eq_mul,Nat.cast_mul,Nat.cast_sub (Fact.out : p.Prime).one_lt.le,Nat.cast_one]
  rw [hleft] at hweighted
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hp1 : 0 < (p : ℝ)-1 := by linarith
  have hp0 : 0 < (p : ℝ) := by linarith
  have hfac : 0 < ((p : ℝ)-1)*(p : ℝ) := mul_pos hp1 hp0
  apply (mul_le_mul_iff_right₀ hfac).mp
  calc
    _ ≤ (d : ℝ)*((d : ℝ)^d*(p : ℝ)^(2*d)) := hweighted.trans
      (mul_le_mul_of_nonneg_left (coefficientSum_moment_le hfp) (Nat.cast_nonneg _))
    _ = (d : ℝ)^(d+1)*(p : ℝ)^(2*d-2)*(p : ℝ)^2 := by
      have hexp : (p : ℝ)^(2*d)=(p : ℝ)^(2*d-2)*(p : ℝ)^2 := by
        rw [← pow_add]
        congr 1
        dsimp [d]
        omega
      rw [hexp,pow_succ]
      ring
    _ ≤ (d : ℝ)^(d+1)*(p : ℝ)^(2*d-2)*(2*(p : ℝ)*((p : ℝ)-1)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    _ = _ := by ring


theorem polynomialSum_linear {q : ℕ} [NeZero q] (f : (ZMod q)[X])
    (hf : f.natDegree=1) : polynomialSum q f=0 := by
  have hc : f.coeff 1 ≠ 0 := by
    rw [← hf]
    exact leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (show 0<f.natDegree by omega))
  have he := eq_X_add_C_of_natDegree_le_one hf.le
  unfold polynomialSum
  have hev (x : ZMod q) : f.eval x=f.coeff 1*x+f.coeff 0 := by
    conv_lhs => rw [he]
    simp
  simp_rw [hev]
  simp only [eval_add,eval_mul,eval_C,eval_X,AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul,GafniTao.wooley_sum_stdAddChar_mul]
  simp [hc]

/-- A real-power form, with an explicit constant depending only on degree. -/
theorem polynomialSum_mordell {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)[X]) (hf : 2 ≤ f.natDegree) (hfp : f.natDegree<p) :
    ‖polynomialSum p f‖ ≤
      (2*(f.natDegree : ℝ)^(f.natDegree+1))^((2*f.natDegree : ℝ)⁻¹)*
        (p : ℝ)^(1-1/(f.natDegree : ℝ)) := by
  let d := f.natDegree
  have hd : (0 : ℝ)<d := by exact_mod_cast (show 0<d by dsimp [d]; omega)
  have hh : ‖polynomialSum p f‖ ≤
      (2*(d : ℝ)^(d+1)*(p : ℝ)^(2*d-2))^((2*(d : ℝ))⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) (by positivity) (by positivity)).mpr
    rw [show 2*(d : ℝ)=((2*d : ℕ) : ℝ) by push_cast; rfl,Real.rpow_natCast]
    exact polynomialSum_mordell_power f hf hfp
  have he : ((2*d-2 : ℕ) : ℝ)*(2*(d : ℝ))⁻¹ = 1-1/(d : ℝ) := by
    rw [Nat.cast_sub (show 2≤2*d by dsimp [d]; omega)]
    push_cast
    field_simp
  calc
    _ ≤ _ := hh
    _ = (2*(d : ℝ)^(d+1))^((2*(d : ℝ))⁻¹)*
        ((p : ℝ)^(2*d-2))^((2*(d : ℝ))⁻¹) :=
      Real.mul_rpow (by positivity) (by positivity)
    _ = _ := by
      congr 1
      rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity),he]

#print axioms affineCoefficients_fiber_card_le
#print axioms polynomialSum_mordell_power
#print axioms polynomialSum_linear
#print axioms polynomialSum_mordell
end Waring.FiniteFieldMordell
