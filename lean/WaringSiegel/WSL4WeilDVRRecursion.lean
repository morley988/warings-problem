import WaringSiegel.WSL4WeilDVRStationary

/-! # Exact singular-branch recursion for mixed cubic sums -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical
open IsLocalRing
open WSL4Local

theorem finite_sum_comp_uniform_fiber
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (g : B → ℂ) (N : ℕ)
    (hN : ∀ y : B, Nat.card {x : A // f x=y}=N) :
    (∑ x : A, g (f x))=(N : ℂ)*∑ y : B, g y := by
  rw [← Fintype.sum_fiberwise' f g]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hN,
    nsmul_eq_mul, ← Finset.mul_sum]

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)]
attribute [local instance] quotientFintype residueFintype

def dvrZeroCubicSum (r : ℕ) (hr : 0<r)
    (ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ) (a b : R) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : R ⧸ maximalIdeal R^r =>
      localResidueReduction _ (Ideal.pow_le_self (by omega)) x=0),
    ψ (Ideal.Quotient.mk _ a*x^3+Ideal.Quotient.mk _ b*x)

theorem dvrCubicSum_last_digit
    {π : R} (hπ : Irreducible π) (r : ℕ) (hr : 2≤r)
    (ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ) (hψ : ψ.IsPrimitive) (a b : R) :
    dvrCubicSum r ψ a b =
      ∑ x ∈ Finset.univ.filter (fun x : R ⧸ maximalIdeal R^r =>
        3*residue R a*(localResidueReduction _ (Ideal.pow_le_self (by omega)) x)^2+
          residue R b=0), ψ (Ideal.Quotient.mk _ a*x^3+Ideal.Quotient.mk _ b*x) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le (show 1≤r by omega)
  have hm : 1≤m := by omega
  rw [dvrCubicSum_stationary_restriction hπ 1 m hm ψ hψ a b]
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factor_mk,localResidueReduction_mk]
  have he1 : 3*Ideal.Quotient.mk (maximalIdeal R^1) a*(Ideal.Quotient.mk _ y)^2+
      Ideal.Quotient.mk _ b=Ideal.Quotient.mk (maximalIdeal R^1) (3*a*y^2+b) := by
    simp only [map_add,map_mul,map_pow,map_ofNat]
  have he2 : 3*residue R a*(residue R y)^2+residue R b=residue R (3*a*y^2+b) := by
    simp only [map_add,map_mul,map_pow,map_ofNat]
  rw [he1,he2,Ideal.Quotient.eq_zero_iff_mem,residue_eq_zero_iff,pow_one]

theorem dvrCubicSum_eq_zero_residue_of_linear_mem
    {π : R} (hπ : Irreducible π) (r : ℕ) (hr : 2≤r)
    (ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ) (hψ : ψ.IsPrimitive)
    (h3 : IsUnit (3 : R)) {a b : R} (ha : IsUnit a) (hb : b∈maximalIdeal R) :
    dvrCubicSum r ψ a b=dvrZeroCubicSum r (by omega) ψ a b := by
  rw [dvrCubicSum_last_digit hπ r hr ψ hψ a b]
  unfold dvrZeroCubicSum
  have h3a : (3 : ResidueField R)*residue R a ≠ 0 := by
    simpa only [map_mul,map_ofNat] using (residue_ne_zero_iff_isUnit (3*a)).mpr (h3.mul ha)
  have hb0 := (residue_eq_zero_iff b).mpr hb
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hb0, add_zero,
    mul_eq_zero, h3a, false_or, pow_eq_zero_iff (by decide : 2≠0)]

theorem dvrZeroCubicSum_scale
    {π : R} (hπ : Irreducible π) (n k : ℕ)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+(k+1))) ℂ)
    (a b a' b' : R)
    (hscale : ∀ y : R, a*(π*y)^3+b*(π*y)=π^(k+1)*(a'*y^3+b'*y)) :
    dvrZeroCubicSum (n+(k+1)) (by omega) ψ a b =
      (Nat.card (ResidueField R) : ℂ)^k *
        dvrCubicSum n (scaledQuotientCharacter hπ (k+1) n ψ) a' b' := by
  let er : (R ⧸ maximalIdeal R^(n+k+1)) ≃+* (R ⧸ maximalIdeal R^(n+(k+1))) :=
    Ideal.quotEquivOfEq (by rw [Nat.add_assoc])
  let e : (R ⧸ maximalIdeal R^(n+k)) ≃
      {z : R ⧸ maximalIdeal R^(n+(k+1)) //
        localResidueReduction _ (Ideal.pow_le_self (by omega)) z=0} :=
    (uniformizerZeroResidueEquiv hπ (n+k)).trans (er.toEquiv.subtypeEquiv (by
      intro z
      obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective z
      simp only [RingEquiv.toEquiv_eq_coe,EquivLike.coe_coe,er,Ideal.quotEquivOfEq_mk,
        localResidueReduction_mk]))
  have hemk (y : R) : (e (Ideal.Quotient.mk (maximalIdeal R^(n+k)) y)).val=
      Ideal.Quotient.mk (maximalIdeal R^(n+(k+1))) (π*y) := by
    change er (Ideal.Quotient.mk (maximalIdeal R^(n+k+1)) (π*y))=_
    exact Ideal.quotEquivOfEq_mk _ _
  let f := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I:=maximalIdeal R) (Nat.le_add_right n k))
  let g : R ⧸ maximalIdeal R^n → ℂ := fun x =>
    scaledQuotientCharacter hπ (k+1) n ψ (Ideal.Quotient.mk _ a'*x^3+Ideal.Quotient.mk _ b'*x)
  have hphase (x : R ⧸ maximalIdeal R^(n+k)) :
      ψ (Ideal.Quotient.mk (maximalIdeal R^(n+(k+1))) a*(e x).val^3+
          Ideal.Quotient.mk _ b*(e x).val)=g (f x) := by
    obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hemk]
    dsimp only [g,f]
    rw [Ideal.Quotient.factor_mk]
    simp only [← map_pow, ← map_mul, ← map_add]
    rw [scaledQuotientCharacter_mk,hscale]
  have hs : dvrZeroCubicSum (n+(k+1)) (by omega) ψ a b =
      ∑ x : R ⧸ maximalIdeal R^(n+k), g (f x) := by
    unfold dvrZeroCubicSum
    rw [Finset.sum_subtype (p:=fun x : R ⧸ maximalIdeal R^(n+(k+1)) =>
      localResidueReduction _ (Ideal.pow_le_self (by omega)) x=0) _
      (by intro x; simp only [Finset.mem_filter,Finset.mem_univ,true_and])]
    rw [← e.sum_comp]
    exact Finset.sum_congr rfl (fun x _ => hphase x)
  rw [hs, finite_sum_comp_uniform_fiber f g (Nat.card (ResidueField R)^k)
    (fun y => dvr_reduction_fiber_card n k y), Nat.cast_pow]
  rfl

theorem dvrCubicSum_three_step
    {π : R} (hπ : Irreducible π) (n : ℕ)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+3)) ℂ) (hψ : ψ.IsPrimitive)
    (h3 : IsUnit (3 : R)) {a : R} (ha : IsUnit a) (b : R) :
    dvrCubicSum (n+3) ψ a (π^2*b) =
      (Nat.card (ResidueField R) : ℂ)^2 *
        dvrCubicSum n (scaledQuotientCharacter hπ 3 n ψ) a b := by
  have hπm : π∈maximalIdeal R := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  rw [dvrCubicSum_eq_zero_residue_of_linear_mem hπ (n+3) (by omega) ψ hψ h3 ha
    (by simpa only [pow_two,mul_assoc] using (maximalIdeal R).mul_mem_right (π*b) hπm)]
  exact dvrZeroCubicSum_scale hπ n 2 ψ a (π^2*b) a b (by intro y; ring)

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_last_digit
#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_three_step
