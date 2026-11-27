import WaringSiegel.WSL3MomentLocalPowerPrimitive
import WaringSiegel.WSL3PowerFiniteDensity

/-!
# Uniform good-prime lower tails for actual all-degree local counts

The finite-field count loses at most the single zero residue tuple when
restricted to primitive solutions. Exact Hensel fibers then transfer this
bound to every positive precision. This is a genuine cofinite Euler-tail
lower estimate, uniform in the local target.
-/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL3

theorem residue_power_count_le_primitive_add_one
    {R : Type*} [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]
    (k s : ℕ) (a : R) :
    Nat.card {x : Fin s → ResidueField R // (∑ i,x i^k)=residue R a} ≤
      Nat.card (PrimitivePowerResidues k R s a)+1 := by
  classical
  letI := Fintype.ofFinite (ResidueField R)
  let Sol := {x : Fin s → ResidueField R // (∑ i,x i^k)=residue R a}
  let Prim := PrimitivePowerResidues k R s a
  letI := Fintype.ofFinite Prim
  let out (x : Sol) : Option Prim :=
    if h : ∃ i,x.val i≠0 then some ⟨x.val,x.property,h⟩ else none
  have hz (x : Sol) (h : ¬∃ i,x.val i≠0) : x.val=0 := by
    funext i
    exact not_ne_iff.mp (fun hi => h ⟨i,hi⟩)
  have hinj : Function.Injective out := by
    intro x y hxy
    by_cases hx : ∃ i,x.val i≠0 <;> by_cases hy : ∃ i,y.val i≠0
    · simp only [out,dif_pos hx,dif_pos hy,Option.some.injEq] at hxy
      exact Subtype.ext (congrArg (fun z : Prim => z.val) hxy)
    · simp only [out,dif_pos hx,dif_neg hy] at hxy
      cases hxy
    · simp only [out,dif_neg hx,dif_pos hy] at hxy
      cases hxy
    · exact Subtype.ext ((hz x hx).trans (hz y hy).symm)
  have h := Nat.card_le_card_of_injective out hinj
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using h

theorem primitive_power_residue_density_lower
    {R : Type*} [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]
    (k s : ℕ) (hk : 0<k) (hs : 1≤s) (a : R) :
    1-((k-1:ℕ):ℝ)^(2*s)/(Nat.card (ResidueField R):ℝ)^(s-1)-
      1/(Nat.card (ResidueField R):ℝ)^(2*s-1) ≤
      (Nat.card (PrimitivePowerResidues k R (2*s) a):ℝ)/
        (Nat.card (ResidueField R):ℝ)^(2*s-1) := by
  letI := Fintype.ofFinite (ResidueField R)
  have herr := (abs_le.mp (finite_field_power_even_normalized_error k s hk hs (residue R a))).1
  simp only [← Nat.card_eq_fintype_card] at herr
  have hcard : (Nat.card {x : Fin (2*s) → ResidueField R // (∑ i,x i^k)=residue R a}:ℝ) ≤
      (Nat.card (PrimitivePowerResidues k R (2*s) a):ℝ)+1 := by
    exact_mod_cast residue_power_count_le_primitive_add_one k (2*s) a
  have hq : 0<(Nat.card (ResidueField R):ℝ) := by exact_mod_cast Nat.card_pos
  have hdiv := div_le_div_of_nonneg_right hcard (pow_pos hq (2*s-1)).le
  rw [add_div] at hdiv
  linarith

theorem primitive_normalized_power_le_full
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (ResidueField R)] (k s n : ℕ) (a : R) :
    normalizedPrimitiveLocalPowerCount k R s n a ≤ normalizedLocalPowerCount R k s (n+1) a := by
  letI := dvr_power_quotient_finite (R := R) (n+1)
  let out : PrimitiveLocalPowerSolutions k R (maximalIdeal R^(n+1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) s a →
      LocalPowerSolutions R (maximalIdeal R^(n+1)) k s a :=
    fun x => ⟨x.val,x.property.1⟩
  have hinj : Function.Injective out := by
    intro x y h
    exact Subtype.ext (congrArg
      (fun z : LocalPowerSolutions R (maximalIdeal R^(n+1)) k s a => z.val) h)
  have h := Nat.card_le_card_of_injective out hinj
  unfold normalizedPrimitiveLocalPowerCount normalizedLocalPowerCount
  apply div_le_div_of_nonneg_right
  · exact_mod_cast h
  · positivity

theorem normalized_local_power_good_tail_lower
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (k s : ℕ) (hk : 0<k) (hs : 1≤s) (hku : IsUnit (k:R)) (n : ℕ) (a : R) :
    1-((k-1:ℕ):ℝ)^(2*s)/(Nat.card (ResidueField R):ℝ)^(s-1)-
      1/(Nat.card (ResidueField R):ℝ)^(2*s-1) ≤
      normalizedLocalPowerCount R k (2*s) (n+1) a := by
  have he := normalized_primitive_local_power_count_eq k hk hku (2*s-1) n a
  have hn : 2*s-1+1=2*s := by omega
  rw [hn] at he
  apply (primitive_power_residue_density_lower k s hk hs a).trans
  rw [← he]
  exact primitive_normalized_power_le_full k (2*s) n a

theorem normalized_local_power_good_square_tail_lower
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (k s : ℕ) (hk : 0<k) (hs : 3≤s) (hku : IsUnit (k:R)) (n : ℕ) (a : R) :
    1-(((k-1:ℕ):ℝ)^(2*s)+1)/(Nat.card (ResidueField R):ℝ)^2 ≤
      normalizedLocalPowerCount R k (2*s) (n+1) a := by
  have hq : 0<(Nat.card (ResidueField R):ℝ) := by exact_mod_cast Nat.card_pos
  have hq1 : 1≤(Nat.card (ResidueField R):ℝ) := by exact_mod_cast Nat.card_pos
  have hpow1 : (Nat.card (ResidueField R):ℝ)^2≤(Nat.card (ResidueField R):ℝ)^(s-1) :=
    pow_le_pow_right₀ hq1 (by omega)
  have hpow2 : (Nat.card (ResidueField R):ℝ)^2≤(Nat.card (ResidueField R):ℝ)^(2*s-1) :=
    pow_le_pow_right₀ hq1 (by omega)
  have h1 := div_le_div_of_nonneg_left (show 0≤((k-1:ℕ):ℝ)^(2*s) by positivity)
    (pow_pos hq 2) hpow1
  have h2 := div_le_div_of_nonneg_left (show (0:ℝ)≤1 by norm_num) (pow_pos hq 2) hpow2
  have hb := normalized_local_power_good_tail_lower k s hk (by omega) hku n a
  rw [add_div]
  linarith

#print axioms normalized_local_power_good_tail_lower
#print axioms normalized_local_power_good_square_tail_lower
end WaringSiegel.WSL3
