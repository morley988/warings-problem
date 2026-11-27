import Waring.EndgameCompletionMinorShift

/-!
# Exact Dirichlet reproduction of nonnegative projected moments

The missing next coefficient is a finite trigonometric polynomial. Its
literal frequency support permits exact reproduction by a Dirichlet
kernel, followed by a nonnegative integral bound.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace Waring.EndgameCompletion
open FourierCompletion QuadraticModulation

def dirichletReproducer (H : Finset ℤ) (u t : ℝ) : ℂ :=
  ∑ h∈H,fourier h (u : UnitAddCircle)*fourier (-h) (t : UnitAddCircle)

theorem dirichletReproducer_eq (H : Finset ℤ) (u t : ℝ) :
    dirichletReproducer H u t=kernel H (t-u) := by
  unfold dirichletReproducer kernel
  apply Finset.sum_congr rfl
  intro h _
  rw [fourier_eq_e,fourier_eq_e,fourier_eq_e,← e_add]
  congr 1
  push_cast
  ring

theorem continuous_dirichletReproducer (H : Finset ℤ) (u : ℝ) :
    Continuous (dirichletReproducer H u) :=
  continuous_finset_sum _ (fun h _=>continuous_const.mul
    ((fourier (-h)).continuous.comp (AddCircle.continuous_mk' 1)))

theorem character_dirichlet_reproduction (H : Finset ℤ) (n : ℤ) (hn : n∈H) (u : ℝ) :
    (∫ t in (0 : ℝ)..1,fourier n (t : UnitAddCircle)*dirichletReproducer H u t)=
      fourier n (u : UnitAddCircle) := by
  have hterm (h : ℤ) : Continuous (fun t : ℝ=>fourier n (t : UnitAddCircle)*
      (fourier h (u : UnitAddCircle)*fourier (-h) (t : UnitAddCircle))) :=
    ((fourier n).continuous.comp (AddCircle.continuous_mk' 1)).mul
      (continuous_const.mul ((fourier (-h)).continuous.comp (AddCircle.continuous_mk' 1)))
  unfold dirichletReproducer
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum (fun h _=>(hterm h).intervalIntegrable 0 1)]
  calc
    _ = ∑ h∈H,fourier h (u : UnitAddCircle)*
        (∫ t in (0 : ℝ)..1,fourier (n-h) (t : UnitAddCircle)) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [sub_eq_add_neg,fourier_add]
      ring
    _ = _ := by
      simp only [interval_integral_character,sub_eq_zero,mul_ite,mul_one,mul_zero]
      simp [hn]

theorem finite_character_dirichlet_reproduction {ι : Type*} [Fintype ι]
    (H : Finset ℤ) (n : ι→ℤ) (w : ι→ℂ) (hn : ∀ i,n i∈H) (u : ℝ) :
    (∫ t in (0 : ℝ)..1,(∑ i,w i*fourier (n i) (t : UnitAddCircle))*
      dirichletReproducer H u t)=∑ i,w i*fourier (n i) (u : UnitAddCircle) := by
  have hi (i : ι) : IntervalIntegrable (fun t : ℝ=>
      w i*fourier (n i) (t : UnitAddCircle)*dirichletReproducer H u t) volume 0 1 :=
    ((continuous_const.mul ((fourier (n i)).continuous.comp (AddCircle.continuous_mk' 1))).mul
      (continuous_dirichletReproducer H u)).intervalIntegrable 0 1
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finset_sum (fun i _=>hi i)]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul,character_dirichlet_reproduction H (n i) (hn i) u]

/-- Exact finite Fourier reproduction bounds any nonnegative real
trigonometric polynomial by its Dirichlet convolution. -/
theorem nonnegative_trig_reproduction {ι : Type*} [Fintype ι]
    (H : Finset ℤ) (n : ι→ℤ) (w : ι→ℂ) (hn : ∀ i,n i∈H)
    (F : ℝ→ℝ) (hF0 : ∀ t,0≤F t)
    (hF : ∀ t,(F t : ℂ)=∑ i,w i*fourier (n i) (t : UnitAddCircle)) (u : ℝ) :
    F u≤∫ t in (0 : ℝ)..1,F t*‖kernel H (t-u)‖ := by
  have he : (∫ t in (0 : ℝ)..1,(F t : ℂ)*dirichletReproducer H u t)=(F u : ℂ) := by
    simp_rw [hF]
    exact finite_character_dirichlet_reproduction H n w hn u
  have hh := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := fun t=>(F t : ℂ)*dirichletReproducer H u t) zero_le_one
  rw [he] at hh
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hF0 _),
    dirichletReproducer_eq] using hh

theorem continuous_e : Continuous e := by unfold e; fun_prop

theorem continuous_projectedMoment {β : Type*} [TopologicalSpace β]
    {ι : Type*} [Fintype ι] (r s : ℕ) (v : ι→ℤ) (w : β→ι→ℂ)
    (hw : ∀ n,Continuous (fun b=>w b n)) :
    Continuous (fun b=>projectedMoment r s v (w b)) := by
  classical
  have he (b : β) : projectedMoment r s v (w b)=
      (∑ x : Fin s→ι,∑ y : Fin s→ι,
        if tuplePowerVector r v x=tuplePowerVector r v y then
          tupleWeight (w b) x*conj (tupleWeight (w b) y) else 0).re := by
    have hh := congrArg Complex.re (projectedMoment_gram r s v (w b))
    simpa only [Complex.ofReal_re] using hh
  simp_rw [he]
  apply Complex.continuous_re.comp
  apply continuous_finset_sum
  intro x _
  apply continuous_finset_sum
  intro y _
  by_cases h : tuplePowerVector r v x=tuplePowerVector r v y
  · simp only [if_pos h,tupleWeight]
    exact (continuous_finset_prod _ (fun i _=>hw (x i))).mul
      ((continuous_finset_prod _ (fun i _=>hw (y i))).star)
  · simp only [if_neg h]
    exact continuous_const

theorem continuous_projectedSlice (r s N : ℕ) :
    Continuous (fun z : ℝ×ℝ=>projectedSlice r s N z.1 z.2) := by
  apply continuous_projectedMoment r s (positiveNode N)
  intro n
  apply continuous_e.comp
  fun_prop

theorem projectedSlice_nonneg (r s N : ℕ) (t θ : ℝ) :
    0≤projectedSlice r s N t θ := projectedMoment_nonneg _ _ _ _

def positivePowerDifference {s N : ℕ} (x y : Fin s→Fin N) (j : ℕ) : ℤ :=
  powerDifference (fun i=>positiveNode N (x i)) (fun i=>positiveNode N (y i)) j

theorem projectedSlice_expansion (r s N : ℕ) (t θ : ℝ) :
    (projectedSlice r s N t θ : ℂ)=
      ∑ x : Fin s→Fin N,∑ y : Fin s→Fin N,
        (if tuplePowerVector r (positiveNode N) x=tuplePowerVector r (positiveNode N) y
          then e (θ*(positivePowerDifference x y (r+2) : ℝ)) else 0)*
        fourier (positivePowerDifference x y (r+1)) (t : UnitAddCircle) := by
  classical
  rw [projectedSlice,projectedMoment_gram]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : tuplePowerVector r (positiveNode N) x=tuplePowerVector r (positiveNode N) y
  · rw [if_pos h,if_pos h,tupleWeight_e_pair,fourier_eq_e,← e_add]
    congr 1
    simp only [positivePowerDifference,powerDifference,GafniTao.wooleyPowerSum,
      Int.cast_sub,Int.cast_sum,Int.cast_pow,Finset.sum_add_distrib,← Finset.mul_sum]
    ring
  · rw [if_neg h,if_neg h,zero_mul]

theorem positivePowerDifference_bound {s N : ℕ} (x y : Fin s→Fin N) (j : ℕ) :
    |positivePowerDifference x y j|≤(s*N^j : ℕ) := by
  have hnode (n : Fin N) : 0≤positiveNode N n ∧ positiveNode N n≤N := by
    dsimp [positiveNode]
    have hn := n.isLt
    constructor <;> omega
  have hsides (z : Fin s→Fin N) :
      0≤GafniTao.wooleyPowerSum (fun i=>positiveNode N (z i)) j ∧
      GafniTao.wooleyPowerSum (fun i=>positiveNode N (z i)) j≤(s*N^j : ℕ) := by
    constructor
    · exact Finset.sum_nonneg (fun i _=>pow_nonneg (hnode (z i)).1 j)
    · calc
        _ ≤ ∑ _i : Fin s,(N : ℤ)^j :=
          Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (hnode (z i)).1 (hnode (z i)).2 j)
        _ = _ := by simp
  have hx := hsides x
  have hy := hsides y
  rw [positivePowerDifference,powerDifference,abs_le]
  constructor <;> omega

theorem projectedSlice_reproduction (r s N : ℕ) (u θ : ℝ) :
    projectedSlice r s N u θ≤
      ∫ t in (0 : ℝ)..1,projectedSlice r s N t θ*
        ‖kernel (Finset.Icc (-(s*N^(r+1) : ℕ) : ℤ) (s*N^(r+1) : ℕ)) (t-u)‖ := by
  classical
  let X := Fin s→Fin N
  let v := fun p : X×X=>positivePowerDifference p.1 p.2 (r+1)
  let w := fun p : X×X=>if tuplePowerVector r (positiveNode N) p.1=
      tuplePowerVector r (positiveNode N) p.2
    then e (θ*(positivePowerDifference p.1 p.2 (r+2) : ℝ)) else 0
  apply nonnegative_trig_reproduction _ v w
    (fun p=>Finset.mem_Icc.mpr (abs_le.mp (positivePowerDifference_bound p.1 p.2 (r+1))))
    (fun t=>projectedSlice r s N t θ)
    (fun t=>projectedSlice_nonneg r s N t θ)
  intro t
  rw [Fintype.sum_prod_type]
  exact projectedSlice_expansion r s N t θ

theorem dirichlet_kernel_le_real_cap (H : ℕ) (B t : ℝ) (hB : 0<B)
    (hHB : ((2*H+1 : ℕ) : ℝ)≤B) :
    ‖kernel (Finset.Icc (-(H : ℤ)) (H : ℤ)) t‖≤
      FiniteSpacing.truncatedReciprocal B⁻¹ (integerDistance t) := by
  have hset : Finset.Icc (-(H : ℤ)) (H : ℤ)=
      Finset.Icc ((-(H : ℤ)-1)+1) ((-(H : ℤ)-1)+(2*H+1 : ℕ)) := by
    congr 1 <;> push_cast <;> ring
  rw [hset,norm_kernel_integer_interval]
  have hl : ‖linearWeylSum (2*H+1) t‖≤linearSumBound (2*H+1) t := by
    rw [← norm_shiftedLinearWeylSum 0]
    exact norm_shiftedLinearWeylSum_le 0 _ _
  apply hl.trans
  unfold linearSumBound FiniteSpacing.truncatedReciprocal
  simp only [one_div,inv_inv]
  split_ifs with hz
  · exact hHB
  · apply min_le_min hHB
    have hd : 0 < integerDistance t := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
    exact inv_anti₀ hd (by linarith)

#print axioms nonnegative_trig_reproduction
#print axioms projectedSlice_reproduction
end Waring.EndgameCompletion
