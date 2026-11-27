import Waring.EndgameCompletionFourier
import Waring.GeometricSums
import Mathlib.Analysis.Convex.Mul

/-!
# Discrete first-derivative cancellation

Finite summation by parts controls a varying linear phase by its chord
distance and the total variation of its increments.  For monomial phases,
the increments are monotone by convexity, so their variation telescopes.
-/

noncomputable section
open scoped BigOperators Classical

namespace Waring.EndgameCompletion
open QuadraticModulation

theorem norm_e_sub_le (x y : ℝ) : ‖e x-e y‖ ≤ 2*Real.pi*|x-y| := by
  have hid : e x-e y=e y*(e (x-y)-1) := by
    rw [mul_sub,← e_add,mul_one,add_sub_cancel]
  rw [hid,norm_mul,norm_e,one_mul]
  have hh : e (x-y)=Complex.exp (((2*(Real.pi*(x-y)) : ℝ) : ℂ)*Complex.I) := by
    unfold e
    congr 1
    push_cast
    ring
  rw [hh,norm_exp_two_mul_I_sub_one]
  calc
    _ ≤ 2*|Real.pi*(x-y)| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = _ := by rw [abs_mul,abs_of_pos Real.pi_pos]; ring

theorem norm_reciprocal_e_sub {D : ℝ} (hD : 0<D) (x y : ℝ)
    (hx : D≤‖e x-1‖) (hy : D≤‖e y-1‖) :
    ‖(e x-1)⁻¹-(e y-1)⁻¹‖ ≤ (2*Real.pi/D^2)*|x-y| := by
  have hx0 : e x-1≠0 := norm_pos_iff.mp (hD.trans_le hx)
  have hy0 : e y-1≠0 := norm_pos_iff.mp (hD.trans_le hy)
  have hid : (e x-1)⁻¹-(e y-1)⁻¹=(e y-e x)/((e x-1)*(e y-1)) := by
    field_simp
    ring
  rw [hid,norm_div,norm_mul]
  calc
    _ ≤ (2*Real.pi*|y-x|)/(‖e x-1‖*‖e y-1‖) :=
      div_le_div_of_nonneg_right (norm_e_sub_le y x) (by positivity)
    _ ≤ (2*Real.pi*|y-x|)/D^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      simpa only [pow_two] using mul_le_mul hx hy hD.le (hD.le.trans hx)
    _ = _ := by rw [abs_sub_comm]; ring

theorem sum_reciprocal_phase_identity (z h : ℕ → ℂ) (N : ℕ)
    (hrel : ∀ n≤N,h n*(z (n+1)-z n)=z n) :
    (∑ n∈Finset.range (N+1),z n)=
      h N*z (N+1)-h 0*z 0-
        ∑ n∈Finset.range N,(h (n+1)-h n)*z (n+1) := by
  induction N with
  | zero => simpa only [Nat.zero_add,Finset.sum_range_zero,Finset.sum_range_one,sub_zero,mul_sub]
      using (hrel 0 le_rfl).symm
  | succ N ih =>
      rw [Finset.sum_range_succ,ih (fun n hn => hrel n (by omega)),Finset.sum_range_succ]
      have hh := hrel (N+1) le_rfl
      linear_combination -hh

theorem norm_sum_varying_phase_le (z : ℕ → ℂ) (δ : ℕ → ℝ)
    (N : ℕ) {D V : ℝ} (hD : 0<D)
    (hz : ∀ n≤N+1,‖z n‖≤1)
    (hstep : ∀ n≤N,z (n+1)=z n*e (δ n))
    (hchord : ∀ n≤N,D≤‖e (δ n)-1‖)
    (hvariation : (∑ n∈Finset.range N,|δ (n+1)-δ n|)≤V) :
    ‖∑ n∈Finset.range (N+1),z n‖ ≤ 2/D+(2*Real.pi/D^2)*V := by
  let h : ℕ → ℂ := fun n => (e (δ n)-1)⁻¹
  have hnonzero (n : ℕ) (hn : n≤N) : e (δ n)-1≠0 :=
    norm_pos_iff.mp (hD.trans_le (hchord n hn))
  have hrel (n : ℕ) (hn : n≤N) : h n*(z (n+1)-z n)=z n := by
    rw [hstep n hn]
    dsimp [h]
    have hid : z n*e (δ n)-z n=z n*(e (δ n)-1) := by ring
    rw [hid,mul_comm (z n),← mul_assoc,inv_mul_cancel₀ (hnonzero n hn),one_mul]
  have hnorm (n : ℕ) (hn : n≤N) : ‖h n‖≤1/D := by
    dsimp [h]
    rw [norm_inv,one_div]
    exact inv_anti₀ hD (hchord n hn)
  have hend (n m : ℕ) (hn : n≤N) (hm : m≤N+1) : ‖h n*z m‖≤1/D := by
    rw [norm_mul]
    exact (mul_le_mul (hnorm n hn) (hz m hm) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hsum : ‖∑ n∈Finset.range N,(h (n+1)-h n)*z (n+1)‖ ≤
      (2*Real.pi/D^2)*V := by
    calc
      _ ≤ ∑ n∈Finset.range N,‖(h (n+1)-h n)*z (n+1)‖ := norm_sum_le _ _
      _ ≤ ∑ n∈Finset.range N,(2*Real.pi/D^2)*|δ (n+1)-δ n| := by
        apply Finset.sum_le_sum
        intro n hn
        have hnlt := Finset.mem_range.mp hn
        rw [norm_mul]
        apply (mul_le_mul_of_nonneg_left (hz (n+1) (by omega)) (norm_nonneg _)).trans
        rw [mul_one]
        exact norm_reciprocal_e_sub hD _ _ (hchord _ (by omega)) (hchord _ (by omega))
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hvariation (by positivity)
  rw [sum_reciprocal_phase_identity z h N hrel]
  calc
    _ ≤ ‖h N*z (N+1)-h 0*z 0‖+
        ‖∑ n∈Finset.range N,(h (n+1)-h n)*z (n+1)‖ := norm_sub_le _ _
    _ ≤ (1/D+1/D)+(2*Real.pi/D^2)*V :=
      add_le_add ((norm_sub_le _ _).trans (add_le_add (hend N (N+1) le_rfl le_rfl)
        (hend 0 0 (Nat.zero_le _) (Nat.zero_le _)))) hsum
    _ = _ := by ring

def monomialIncrement (k n : ℕ) : ℝ := ((n+1 : ℕ) : ℝ)^k-(n : ℝ)^k

theorem monomialIncrement_nonneg (k n : ℕ) : 0≤monomialIncrement k n := by
  unfold monomialIncrement
  apply sub_nonneg.mpr
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ n) _

theorem monomialIncrement_monotone (k : ℕ) : Monotone (monomialIncrement k) := by
  apply monotone_nat_of_le_succ
  intro n
  have hc : ((1/2 : ℝ)•(n : ℝ)+(1/2 : ℝ)•((n+2 : ℕ) : ℝ))^k ≤
      (1/2 : ℝ)•(n : ℝ)^k+(1/2 : ℝ)•((n+2 : ℕ) : ℝ)^k :=
    (convexOn_pow (𝕜 := ℝ) k).2
      (show (n : ℝ)∈Set.Ici 0 from Nat.cast_nonneg (α := ℝ) n)
      (show ((n+2 : ℕ) : ℝ)∈Set.Ici 0 from Nat.cast_nonneg (α := ℝ) (n+2))
      (by norm_num) (by norm_num) (by norm_num)
  have hmid : (1/2 : ℝ)•(n : ℝ)+(1/2 : ℝ)•((n+2 : ℕ) : ℝ)=(n+1 : ℕ) := by
    simp only [smul_eq_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring
  rw [hmid,smul_eq_mul,smul_eq_mul] at hc
  unfold monomialIncrement
  have heq : n+1+1=n+2 := by omega
  rw [heq]
  linarith

theorem monomialIncrement_le (k n : ℕ) :
    monomialIncrement k n ≤ (k : ℝ)*((n+1 : ℕ) : ℝ)^(k-1) := by
  have h := abs_pow_sub_pow_le (a := ((n+1 : ℕ) : ℝ)) (b := (n : ℝ)) (n := k)
  have hpos : (n : ℝ)≤((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change |monomialIncrement k n|≤_ at h
  simpa only [abs_of_nonneg (monomialIncrement_nonneg k n),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n+1)),abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
    max_eq_left hpos,show ((n+1 : ℕ) : ℝ)-(n : ℝ)=1 by push_cast; ring,
    abs_one,one_mul] using h

theorem monomial_phase_increment_variation (k N : ℕ) (β θ : ℝ) :
    (∑ n∈Finset.range N,
      |(β*monomialIncrement k (n+1)-θ)-(β*monomialIncrement k n-θ)|) ≤
      |β| *(k : ℝ)*((N+1 : ℕ) : ℝ)^(k-1) := by
  have heq (n : ℕ) :
      |(β*monomialIncrement k (n+1)-θ)-(β*monomialIncrement k n-θ)| =
        |β| *(monomialIncrement k (n+1)-monomialIncrement k n) := by
    rw [show (β*monomialIncrement k (n+1)-θ)-(β*monomialIncrement k n-θ)=
      β*(monomialIncrement k (n+1)-monomialIncrement k n) by ring,abs_mul,
      abs_of_nonneg (sub_nonneg.mpr (monomialIncrement_monotone k (Nat.le_succ n)))]
  simp_rw [heq]
  rw [← Finset.mul_sum,Finset.sum_range_sub]
  calc
    _ ≤ |β| *monomialIncrement k N := mul_le_mul_of_nonneg_left
      (sub_le_self _ (monomialIncrement_nonneg k 0)) (abs_nonneg _)
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (monomialIncrement_le k N) (abs_nonneg β)

theorem integerDistance_le_add_abs_sub (x y : ℝ) :
    integerDistance x≤ integerDistance y+|x-y| := by
  unfold integerDistance
  exact (round_le x (round y)).trans ((abs_sub_le x y (round y)).trans_eq (add_comm _ _))

theorem integerDistance_neg_eq (x : ℝ) : integerDistance (-x)=integerDistance x := by
  have hh (y : ℝ) : integerDistance (-y)≤ integerDistance y := by
    have h := round_le (-y) (-round y)
    simpa only [integerDistance,Int.cast_neg,neg_sub_neg,abs_sub_comm] using h
  exact le_antisymm (hh x) (by simpa only [neg_neg] using hh (-x))

theorem e_eq_unitCharacter (t : ℝ) : e t=unitCharacter t := by
  unfold e unitCharacter
  simpa only [Int.cast_one,mul_one] using exp_linear_eq_fourier t 1

/-- A discrete first-derivative estimate for an actual monomial plus a
linear twist. The monomial derivative is smaller than half the distance
of the linear frequency to the nearest integer. -/
theorem norm_monomial_linear_sum_le (k N : ℕ) (hN : 1≤N) (β θ : ℝ)
    (hθ : 0< integerDistance θ)
    (hsmall : |β| *(k : ℝ)*(N : ℝ)^(k-1)≤ integerDistance θ/2) :
    ‖∑ n∈Finset.range N,e (β*(n : ℝ)^k-θ*n)‖ ≤
      (1+Real.pi/4)/integerDistance θ := by
  let z : ℕ → ℂ := fun n => e (β*(n : ℝ)^k-θ*n)
  let δ : ℕ → ℝ := fun n => β*monomialIncrement k n-θ
  let V : ℝ := |β| *(k : ℝ)*(N : ℝ)^(k-1)
  have hstep (n : ℕ) : z (n+1)=z n*e (δ n) := by
    dsimp [z,δ,monomialIncrement]
    rw [← e_add]
    congr 1
    push_cast
    ring
  have hperturb (n : ℕ) (hn : n≤N-1) : |δ n-(-θ)|≤V := by
    dsimp [δ,V]
    rw [sub_neg_eq_add,sub_add_cancel,abs_mul,abs_of_nonneg (monomialIncrement_nonneg k n)]
    calc
      _ ≤ |β| *((k : ℝ)*((n+1 : ℕ) : ℝ)^(k-1)) :=
        mul_le_mul_of_nonneg_left (monomialIncrement_le k n) (abs_nonneg _)
      _ ≤ _ := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show n+1≤N by omega)) _
  have hchord (n : ℕ) (hn : n≤N-1) : 2*integerDistance θ≤‖e (δ n)-1‖ := by
    have hdist := integerDistance_le_add_abs_sub (-θ) (δ n)
    rw [integerDistance_neg_eq,abs_sub_comm] at hdist
    have hlower := chord_distance_lower (δ n)
    rw [← e_eq_unitCharacter] at hlower
    have hpert := hperturb n hn
    change V≤ integerDistance θ/2 at hsmall
    linarith
  have hvar : (∑ n∈Finset.range (N-1),|δ (n+1)-δ n|)≤V := by
    simpa only [δ,V,Nat.sub_add_cancel hN] using monomial_phase_increment_variation k (N-1) β θ
  have h := norm_sum_varying_phase_le z δ (N-1) (D := 2*integerDistance θ)
    (V := V) (by positivity) (fun n _ => (norm_e _).le)
    (fun n _ => hstep n) hchord hvar
  simp only [Nat.sub_add_cancel hN] at h
  apply h.trans
  have hbound : 2/(2*integerDistance θ)+(2*Real.pi/(2*integerDistance θ)^2)*V ≤
      2/(2*integerDistance θ)+(2*Real.pi/(2*integerDistance θ)^2)*(integerDistance θ/2) := by
    gcongr
  apply hbound.trans_eq
  field_simp
  ring

theorem norm_monomial_positive_sum_le (k N : ℕ) (β θ : ℝ)
    (hθ : 0< integerDistance θ)
    (hsmall : |β| *(k : ℝ)*(N : ℝ)^(k-1)≤ integerDistance θ/2) :
    ‖∑ n∈Finset.Icc 1 N,e (β*(n : ℝ)^k-θ*n)‖ ≤
      2+(1+Real.pi/4)/integerDistance θ := by
  by_cases hN : N=0
  · subst N
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0<1),Finset.sum_empty,norm_zero]
    positivity
  have hN1 : 1≤N := by omega
  have hsum := norm_monomial_linear_sum_le k N hN1 β θ hθ hsmall
  have hid : (∑ n∈Finset.Icc 1 N,e (β*(n : ℝ)^k-θ*n)) =
      (∑ n∈Finset.range N,e (β*(n : ℝ)^k-θ*n))+
        e (β*(N : ℝ)^k-θ*N)-e (β*(0 : ℝ)^k-θ*0) := by
    rw [← Finset.Ico_succ_right_eq_Icc,Order.succ_eq_add_one,Finset.sum_Ico_eq_sub _ (by omega : 1≤N+1),
      Finset.sum_range_succ,Finset.sum_range_one]
    simp only [Nat.cast_zero]
  rw [hid]
  calc
    _ ≤ ‖(∑ n∈Finset.range N,e (β*(n : ℝ)^k-θ*n))+e (β*(N : ℝ)^k-θ*N)‖+
        ‖e (β*(0 : ℝ)^k-θ*0)‖ := norm_sub_le _ _
    _ ≤ (‖∑ n∈Finset.range N,e (β*(n : ℝ)^k-θ*n)‖+‖e (β*(N : ℝ)^k-θ*N)‖)+
        ‖e (β*(0 : ℝ)^k-θ*0)‖ := add_le_add_right (norm_add_le _ _) _
    _ ≤ _ := by simp only [norm_e]; linarith

theorem completedLinearSum_monomial_eq (q k : ℕ) [NeZero q]
    (P β : ℝ) (b : ZMod q) :
    completedLinearSum q (ordinaryNumbers P) (fun n=>e (β*(n : ℝ)^k)) b =
      ∑ n∈Finset.Icc 1 ⌊P⌋₊,e (β*(n : ℝ)^k-((b.val : ℝ)/q)*n) := by
  unfold completedLinearSum ordinaryNumbers
  apply Finset.sum_congr rfl
  intro n _
  have hs : ZMod.stdAddChar (-b*(n : ZMod q))=e ((-(b.val : ℝ)/q)*(n : ℝ)) := by
    simpa only [pow_one,Int.cast_neg,Int.cast_natCast,ZMod.natCast_zmod_val] using
      stdAddChar_monomial_nat q 1 (-(b.val : ℤ)) n
  rw [hs,← e_add]
  congr 1
  ring

/-- The completed nonzero frequencies on the broad rational arcs have the
required q/min(b,q-b) bound, uniformly in the length and monomial phase. -/
theorem completedLinearSum_broad_bound (q k : ℕ) [NeZero q]
    {P β : ℝ} (hP : 0≤P) (b : ZMod q) (hb : b≠0)
    (hβ : |β| *(k : ℝ)*P^(k-1)≤1/(2*(q : ℝ))) :
    ‖completedLinearSum q (ordinaryNumbers P) (fun n=>e (β*(n : ℝ)^k)) b‖ ≤
      2+(1+Real.pi/4)*(q : ℝ)/(min b.val (q-b.val) : ℕ) := by
  have hq : (0 : ℝ)<q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hbpos : 0<b.val := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hb
    exact ZMod.val_injective _ (by simpa only [ZMod.val_zero] using hz)
  have hd : 0<min b.val (q-b.val) := lt_min hbpos (Nat.sub_pos_of_lt b.val_lt)
  have hdR : (0 : ℝ)<(min b.val (q-b.val) : ℕ) := by exact_mod_cast hd
  have hdist : integerDistance ((b.val : ℝ)/q)=((min b.val (q-b.val) : ℕ) : ℝ)/q := by
    simpa only [integerDistance,Nat.mod_eq_of_lt b.val_lt] using
      (abs_sub_round_div_natCast_eq (α := ℝ) (m := b.val) (n := q))
  have hθ : 0< integerDistance ((b.val : ℝ)/q) := by rw [hdist]; positivity
  have hsmall : |β| *(k : ℝ)*(⌊P⌋₊ : ℝ)^(k-1)≤ integerDistance ((b.val : ℝ)/q)/2 := by
    calc
      _ ≤ |β| *(k : ℝ)*P^(k-1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hP) _) (by positivity)
      _ ≤ 1/(2*(q : ℝ)) := hβ
      _ ≤ _ := by
        rw [hdist]
        have hd1 : (1 : ℝ)≤(min b.val (q-b.val) : ℕ) := by exact_mod_cast hd
        apply (le_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
        apply (le_div_iff₀ hq).mpr
        field_simp
        linarith
  rw [completedLinearSum_monomial_eq]
  apply (norm_monomial_positive_sum_le k ⌊P⌋₊ β ((b.val : ℝ)/q) hθ hsmall).trans_eq
  rw [hdist]
  field_simp

#print axioms norm_sum_varying_phase_le
#print axioms monomial_phase_increment_variation
#print axioms norm_monomial_linear_sum_le
#print axioms completedLinearSum_broad_bound

end Waring.EndgameCompletion
