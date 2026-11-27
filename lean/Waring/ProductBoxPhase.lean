import Waring.ProductBoxQuadrature

/-! # Actual product phases satisfy the quadrature hypotheses -/

noncomputable section
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion QuadraticModulation

def productPhase (k L : ℕ) (β : ℝ) (x : Fin L → ℝ) : ℂ := e (β*(∏ i,x i)^k)

theorem continuous_productPhase (k L : ℕ) (β : ℝ) : Continuous (productPhase k L β) := by
  unfold productPhase e
  fun_prop

theorem productPhase_cons (k L : ℕ) (β t : ℝ) (y : Fin L → ℝ) :
    productPhase k (L+1) β (Fin.cons t y)=productPhase k L (β*t^k) y := by
  unfold productPhase
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_pow]
  congr 1
  ring

theorem productPhase_head (k L : ℕ) (β : ℝ) (y : Fin L → ℝ) :
    (fun t : ℝ => productPhase k (L+1) β (Fin.cons t y))=
      (fun t : ℝ => e ((β*(∏ i,y i)^k)*t^k)) := by
  funext t
  rw [productPhase_cons,productPhase]
  congr 1
  ring

theorem monomial_derivative_of_scale {k : ℕ} (hk : 1≤k) {M A β : ℝ}
    (hM : 0<M) (hA : |β| *M^k≤A) {t : ℝ} (ht : t ∈ Set.Icc 0 M) :
    ‖deriv (fun x : ℝ => e (β*x^k)) t‖≤2*Real.pi*(k : ℝ)*A/M := by
  apply (norm_deriv_monomial_e_le k β ht).trans
  apply (le_div_iff₀ hM).mpr
  calc
    _ = (2*Real.pi*(k : ℝ))*(|β| *M^k) := by
      have he : M^(k-1)*M=M^k := by rw [← pow_succ,Nat.sub_add_cancel hk]
      calc
        _ = (2*Real.pi*(k : ℝ))*|β| *(M^(k-1)*M) := by ring
        _ = _ := by rw [he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)

theorem productPhase_regular (k L : ℕ) (hk : 1≤k) {M A β : ℝ}
    (hM : 0<M) (hA : |β| *M^(k*L)≤A) :
    BoxRegular L M 1 (2*Real.pi*(k : ℝ)*A/M) (productPhase k L β) := by
  induction L generalizing β with
  | zero => trivial
  | succ L ih =>
    constructor
    · intro y hy
      have hy0 : 0≤∏ i,y i := Finset.prod_nonneg (fun i _ => (hy i).1)
      have hyM : (∏ i,y i)≤M^L := by
        calc
          _ ≤ ∏ _i : Fin L,M := Finset.prod_le_prod (fun i _ => (hy i).1) (fun i _ => (hy i).2)
          _ = _ := by simp
      have hA' : |β*(∏ i,y i)^k| *M^k≤A := by
        rw [abs_mul,abs_of_nonneg (pow_nonneg hy0 _)]
        calc
          _ ≤ |β| *(M^L)^k*M^k := by gcongr
          _ = |β| *M^(k*(L+1)) := by rw [← pow_mul,mul_assoc,← pow_add]; congr 2 <;> ring
          _ ≤ A := hA
      rw [productPhase_head]
      exact ⟨fun t => (hasDerivAt_monomial_e k _ t).differentiableAt,
        continuous_deriv_monomial_e k _,by change ‖e _‖≤1; rw [norm_e],
        fun t ht => monomial_derivative_of_scale hk hM hA' ht⟩
    · intro t ht
      have hA' : |β*t^k| *M^(k*L)≤A := by
        rw [abs_mul,abs_of_nonneg (pow_nonneg ht.1 _)]
        calc
          _ ≤ |β| *M^k*M^(k*L) := by gcongr <;> first | exact ht.1 | exact ht.2
          _ = |β| *M^(k*(L+1)) := by rw [mul_assoc,← pow_add]; congr 2 <;> ring
          _ ≤ A := hA
      simpa only [productPhase_cons] using ih hA'

theorem rational_product_periodic (k L : ℕ) (a : ℤ) {q : ℕ} (hq : 0<q) :
    GridPeriodic L q (fun x : Fin L → ℕ => productPhase k L ((a : ℝ)/q) (fun i => x i)) := by
  induction L generalizing a with
  | zero => trivial
  | succ L ih =>
    constructor
    · intro y
      have he : (fun n : ℕ => productPhase k (L+1) ((a : ℝ)/q) (fun i : Fin (L+1) => (((Fin.cons n y : Fin (L+1) → ℕ) i) : ℝ)))=
          (fun n : ℕ => e (((a*(∏ i,(y i : ℤ))^k : ℤ) : ℝ)/q*(n : ℝ)^k)) := by
        funext n
        unfold productPhase
        simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
        push_cast
        congr 1
        ring
      rw [he]
      exact rational_monomial_periodic k _ hq
    · intro n
      convert ih (a*(n : ℤ)^k) using 1
      funext y
      unfold productPhase
      simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
      push_cast
      congr 1
      ring

#print axioms productPhase_regular
#print axioms rational_product_periodic
end Waring.ProductBox
