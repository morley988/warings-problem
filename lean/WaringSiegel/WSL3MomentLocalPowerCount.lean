import WaringSiegel.WSL3MomentLocalPowerLift

/-!
# Actual all-degree local counts at primes where the exponent is a unit

Each free coordinate varies independently modulo m^n; exact Hensel lifting
restores the remaining coordinate. Injectivity is proved in the actual
quotient, so the resulting count is not a formal density parameter.
-/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL3

def LocalPowerSolutions (R : Type*) [CommRing R] (I : Ideal R) (k s : ℕ) (a : R) :=
  {x : Fin s → R ⧸ I // (∑ i,x i^k)=Ideal.Quotient.mk I a}

def localPowerSolutionCount (R : Type*) [CommRing R] (I : Ideal R) (k s : ℕ) (a : R) : ℕ :=
  Nat.card (LocalPowerSolutions R I k s a)

instance localPowerSolutions_finite
    {R : Type*} [CommRing R] (I : Ideal R) (k s : ℕ) (a : R) [Finite (R ⧸ I)] :
    Finite (LocalPowerSolutions R I k s a) := by
  unfold LocalPowerSolutions
  infer_instance

theorem local_power_count_lower_of_unit_tuple
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (k : ℕ) (hk : 0<k) (hku : IsUnit (k:R))
    {s : ℕ} (x : Fin (s+1) → R) (hx : IsUnit (x 0)) (n : ℕ) :
    Nat.card (ResidueField R)^(s*n) ≤
      localPowerSolutionCount R (maximalIdeal R^(n+1)) k (s+1) (∑ i,x i^k) := by
  classical
  letI := dvr_power_quotient_finite (R := R) (n+1)
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπm : π∈maximalIdeal R := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  choose rep hrep using
    (fun b : R ⧸ maximalIdeal R^n => Ideal.Quotient.mk_surjective b)
  let y (b : Fin s → R ⧸ maximalIdeal R^n) (i : Fin s) : R :=
    x i.succ+π*rep (b i)
  have hy (b : Fin s → R ⧸ maximalIdeal R^n) (i : Fin s) :
      y b i-x i.succ∈maximalIdeal R := by
    simp only [y,add_sub_cancel_left]
    exact (maximalIdeal R).mul_mem_right _ hπm
  have hzexists (b : Fin s → R ⧸ maximalIdeal R^n) :
      ∃ z : R,z^k+∑ i,y b i^k=∑ i,x i^k ∧ IsUnit z :=
    power_sum_adjust_free_coordinates k hk hku x hx (y b) (hy b)
  choose z hz hzu using hzexists
  let out (b : Fin s → R ⧸ maximalIdeal R^n) :
      LocalPowerSolutions R (maximalIdeal R^(n+1)) k (s+1) (∑ i,x i^k) :=
    ⟨fun i => Ideal.Quotient.mk (maximalIdeal R^(n+1))
      ((Fin.cons (z b) (y b) : Fin (s+1) → R) i),by
        have hh : (∑ i,(Fin.cons (z b) (y b) i)^k)=∑ i,x i^k := by
          simpa only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ] using hz b
        simpa only [map_sum,map_pow] using
          congrArg (Ideal.Quotient.mk (maximalIdeal R^(n+1))) hh⟩
  have hout : Function.Injective out := by
    intro b d hbd
    funext i
    have hi := congrArg (fun t => t.val i.succ) hbd
    change Ideal.Quotient.mk (maximalIdeal R^(n+1)) (y b i)=
      Ideal.Quotient.mk (maximalIdeal R^(n+1)) (y d i) at hi
    have hdiff : π*(rep (b i)-rep (d i))∈maximalIdeal R^(n+1) := by
      convert Ideal.Quotient.eq.mp hi using 1 <;> dsimp [y] <;> ring
    have hsmall := (uniformizer_power_cancel_mem hπ 1 n).mp (by simpa only [pow_one] using hdiff)
    have hquot := Ideal.Quotient.eq.mpr hsmall
    simpa only [hrep] using hquot
  calc
    Nat.card (ResidueField R)^(s*n)=Nat.card (Fin s → R ⧸ maximalIdeal R^n) := by
      rw [Nat.card_fun,Nat.card_fin,dvr_power_quotient_card,← pow_mul,Nat.mul_comm]
    _ ≤ _ := Nat.card_le_card_of_injective out hout

def normalizedLocalPowerCount
    (R : Type*) [CommRing R] [IsLocalRing R] (k s e : ℕ) (a : R) : ℝ :=
  (localPowerSolutionCount R (maximalIdeal R^e) k s a : ℝ)/
    (Nat.card (ResidueField R) : ℝ)^((s-1)*e)

theorem normalized_local_power_count_lower_of_unit_tuple
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (k : ℕ) (hk : 0<k) (hku : IsUnit (k:R))
    {s : ℕ} (x : Fin (s+1) → R) (hx : IsUnit (x 0)) (n : ℕ) :
    1/(Nat.card (ResidueField R) : ℝ)^s ≤
      normalizedLocalPowerCount R k (s+1) (n+1) (∑ i,x i^k) := by
  have hq : 0<(Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  have hcount : (Nat.card (ResidueField R) : ℝ)^(s*n) ≤
      (localPowerSolutionCount R (maximalIdeal R^(n+1)) k (s+1) (∑ i,x i^k) : ℝ) := by
    exact_mod_cast local_power_count_lower_of_unit_tuple k hk hku x hx n
  unfold normalizedLocalPowerCount
  rw [Nat.add_sub_cancel]
  calc
    1/(Nat.card (ResidueField R) : ℝ)^s =
      (Nat.card (ResidueField R) : ℝ)^(s*n)/(Nat.card (ResidueField R) : ℝ)^(s*(n+1)) := by
        rw [Nat.mul_add,Nat.mul_one,pow_add,← div_div,div_self (pow_ne_zero _ hq.ne')]
    _ ≤ _ := div_le_div_of_nonneg_right hcount (pow_pos hq _).le

#print axioms local_power_count_lower_of_unit_tuple
#print axioms normalized_local_power_count_lower_of_unit_tuple
end WaringSiegel.WSL3
