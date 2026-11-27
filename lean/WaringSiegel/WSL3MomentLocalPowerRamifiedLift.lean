import WaringSiegel.WSL3MomentLocalPowerLift

/-! # A unit-linear correction equation in every Henselian local ring -/
noncomputable section
set_option maxHeartbeats 1400000
open Polynomial IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL3

/-- Reciprocal monic-polynomial trick, valid without assuming the degree
is a unit. This is the ramified Hensel input. -/
theorem unit_linear_correction_surjective
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (N : ℕ) (A : ℕ → R) {c : R} (hc : c∈maximalIdeal R) :
    ∃ t : R,t∈maximalIdeal R ∧ t+∑ j∈Finset.range N,A j*t^(j+2)=c := by
  let g : R[X] := ∑ j∈Finset.range N,C (A j*c^(j+1))*X^(N-1-j)
  let f : R[X] := X^(N+1)-(X^N+g)
  have hg : g.degree<(N+1:ℕ) := by
    have hle : g.degree≤(N:WithBot ℕ) := by
      apply (degree_sum_le _ _).trans
      apply Finset.sup_le
      intro j hj
      apply (degree_C_mul_X_pow_le _ _).trans
      exact_mod_cast (show N-1-j≤N by omega)
    exact hle.trans_lt (by exact_mod_cast Nat.lt_succ_self N)
  have hf : f.Monic := by
    apply monic_X_pow_sub
    have hX : (X^N:R[X]).degree<(N+1:ℕ) := by
      rw [degree_X_pow]
      exact_mod_cast Nat.lt_succ_self N
    exact (degree_add_le _ _).trans_lt (max_lt hX hg)
  have hc0 : residue R c=0 := (residue_eq_zero_iff c).mpr hc
  have hroot : aeval (1:ResidueField R) f=0 := by
    simp [f,g,hc0]
  have hder : aeval (1:ResidueField R) f.derivative≠0 := by
    have he : aeval (1:ResidueField R) f.derivative=1 := by
      simp [f,g,derivative_pow,derivative_sum,derivative_mul,hc0]
    rw [he]
    exact one_ne_zero
  have hH := ((HenselianLocalRing.TFAE R).out 0 1).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨w,hw,hwr⟩ := hH f hf 1 hroot hder
  have hwu : IsUnit w := (residue_ne_zero_iff_isUnit w).mp (by rw [hwr]; exact one_ne_zero)
  have hw0 : w^(N+1)=w^N+∑ j∈Finset.range N,A j*c^(j+1)*w^(N-1-j) := by
    apply sub_eq_zero.mp
    simpa [f,g,Polynomial.IsRoot,eval_finset_sum] using hw
  let t : R := c*↑hwu.unit⁻¹
  have hwt : w*t=c := by
    have hinv : w*↑hwu.unit⁻¹=1 := by
      simpa only [hwu.unit_spec] using Units.mul_inv hwu.unit
    calc
      w*t=c*(w*↑hwu.unit⁻¹) := by dsimp [t]; ring
      _=c := by rw [hinv,mul_one]
  have hterm (j : ℕ) (hj : j∈Finset.range N) :
      w^(N+1)*(A j*t^(j+2))=c*(A j*c^(j+1)*w^(N-1-j)) := by
    have hjN := Finset.mem_range.mp hj
    have hp : w^(N+1)=w^(j+2)*w^(N-1-j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp,← hwt,mul_pow w t (j+1),pow_succ w (j+1),pow_succ t (j+1)]
    ring
  have he : t+∑ j∈Finset.range N,A j*t^(j+2)=c := by
    apply (hwu.pow (N+1)).mul_left_cancel
    calc
      w^(N+1)*(t+∑ j∈Finset.range N,A j*t^(j+2)) =
          c*(w^N+∑ j∈Finset.range N,A j*c^(j+1)*w^(N-1-j)) := by
        rw [mul_add,mul_add,Finset.mul_sum,Finset.mul_sum]
        congr 1
        · rw [pow_succ,← hwt]
          ring
        · exact Finset.sum_congr rfl hterm
      _=w^(N+1)*c := by rw [← hw0]; ring
  exact ⟨t,(maximalIdeal R).mul_mem_right _ hc,he⟩

theorem unit_power_correction_identity
    {R : Type*} [CommRing R] (N : ℕ) (t : R) :
    (1+(N+1:R)*t)^(N+1)=1+(N+1:R)^2*
      (t+∑ j∈Finset.range N,((N+1).choose (j+2):R)*(N+1:R)^j*t^(j+2)) := by
  have hexp : (1+(N+1:R)*t)^(N+1)=
      1+(N+1:R)^2*t+
        ∑ j∈Finset.range N,(N+1:R)^(j+2)*t^(j+2)*((N+1).choose (j+2):R) := by
    rw [add_comm (1:R),add_pow,show N+1+1=2+N by omega,Finset.sum_range_add]
    simp only [one_pow,mul_one,mul_pow]
    rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [pow_zero,pow_one,Nat.choose_zero_right,Nat.choose_one_right,
      Nat.cast_one,zero_add,one_mul]
    have hs : (∑ j∈Finset.range N,(N+1:R)^(2+j)*t^(2+j)*((N+1).choose (2+j):R))=
        ∑ j∈Finset.range N,(N+1:R)^(j+2)*t^(j+2)*((N+1).choose (j+2):R) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.add_comm 2 j]
    rw [hs]
    push_cast
    ring
  rw [hexp,mul_add,Finset.mul_sum,← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

theorem one_power_square_maximalIdeal_perturbation
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (k : ℕ) (hk : 0<k) {c : R} (hc : c∈maximalIdeal R) :
    ∃ y : R,y^k=1+(k:R)^2*c ∧ residue R y=1 ∧ IsUnit y := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨t,htm,ht⟩ := unit_linear_correction_surjective N
    (fun j => ((N+1).choose (j+2):R)*(N+1:R)^j) hc
  have htr : residue R t=0 := (residue_eq_zero_iff t).mpr htm
  have hyr : residue R (1+(N+1:R)*t)=1 := by simp [htr]
  refine ⟨1+(N+1:R)*t,?_,hyr,(residue_ne_zero_iff_isUnit _).mp (by rw [hyr]; exact one_ne_zero)⟩
  rw [unit_power_correction_identity,ht]
  simp only [Nat.cast_succ]

#print axioms unit_linear_correction_surjective
#print axioms one_power_square_maximalIdeal_perturbation
end WaringSiegel.WSL3
