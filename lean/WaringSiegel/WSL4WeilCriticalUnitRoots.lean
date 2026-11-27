import WaringSiegel.WSL4WeilUnitRootKernel

/-! # Uniform counts for cubic critical points among local units -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical
open IsLocalRing WSL3
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]
attribute [local instance] quotientFintype residueFintype

theorem nat_factor_cancel_mem (k : ℕ) (hk : (k:R)≠0) (n : ℕ) (d : R) :
    (k:R)*d ∈ maximalIdeal R^(n+powerDerivativeOrder R k) ↔
      d ∈ maximalIdeal R^n := by
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨t,u,hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hk hπ
  have ht : powerDerivativeOrder R k=t := by
    simp only [powerDerivativeOrder,IsDiscreteValuationRing.addVal_def _ u hπ t hu,
      ENat.toNat_coe]
  rw [ht,hu,mul_assoc]
  rw [(maximalIdeal R^(n+t)).unit_mul_mem_iff_mem u.isUnit]
  exact uniformizer_power_cancel_mem hπ t n

theorem cubic_critical_unit_count_at_offset
    (h2 : (2:R)≠0) (h3 : (3:R)≠0) (n : ℕ) {a : R} (ha : IsUnit a) (b : R) :
    (Finset.univ.filter (fun x : R ⧸ maximalIdeal R^(n+powerDerivativeOrder R 3) =>
      IsUnit x ∧ 3*Ideal.Quotient.mk _ a*x^2+Ideal.Quotient.mk _ b=0)).card ≤
      Nat.card (ResidueField R)^(powerDerivativeOrder R 3+powerLocalPrecision R 2) := by
  let t := powerDerivativeOrder R 3
  let f := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I:=maximalIdeal R) (Nat.le_add_right n t))
  let P : R ⧸ maximalIdeal R^(n+t) → Prop := fun x =>
    IsUnit x ∧ 3*Ideal.Quotient.mk _ a*x^2+Ideal.Quotient.mk _ b=0
  change (Finset.univ.filter P).card ≤ _
  by_cases hz : ∃z,P z
  · obtain ⟨z,hz⟩ := hz
    have hfz : IsUnit (f z) := hz.1.map f
    have hsub : Finset.univ.filter P ⊆
        Finset.univ.filter (fun x => (f x)^2=(f z)^2) := by
      intro x hx
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
      obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective z
      have he : 3*a*(x^2-z^2) ∈ maximalIdeal R^(n+t) := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simp only [map_mul,map_sub,map_pow,map_ofNat]
        dsimp [P] at hx hz
        linear_combination hx.2-hz.2
      have he' : (3:R)*(x^2-z^2) ∈ maximalIdeal R^(n+t) := by
        apply (Ideal.unit_mul_mem_iff_mem _ ha).mp
        convert he using 1 <;> ring
      have hl := (nat_factor_cancel_mem 3 h3 n (x^2-z^2)).mp he'
      change (Ideal.Quotient.factor _ (Ideal.Quotient.mk _ x))^2=
        (Ideal.Quotient.factor _ (Ideal.Quotient.mk _ z))^2
      simp only [Ideal.Quotient.factor_mk,← map_pow,Ideal.Quotient.eq]
      exact hl
    have hc := finite_predicate_preimage_card f (fun x => x^2=(f z)^2)
      (Nat.card (ResidueField R)^t) (fun y => dvr_reduction_fiber_card n t y)
    calc
      _ ≤ (Finset.univ.filter (fun x => (f x)^2=(f z)^2)).card := Finset.card_le_card hsub
      _ = (Finset.univ.filter (fun x => x^2=(f z)^2)).card*Nat.card (ResidueField R)^t := hc
      _ ≤ Nat.card (ResidueField R)^powerLocalPrecision R 2*Nat.card (ResidueField R)^t :=
        Nat.mul_le_mul_right _ (square_roots_count_bound_of_unit_root h2 n hfz)
      _ = _ := by rw [← pow_add,Nat.add_comm]
  · have he : Finset.univ.filter P=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hz ⟨x,(Finset.mem_filter.mp hx).2⟩
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

theorem cubic_critical_unit_count_uniform
    (h2 : (2:R)≠0) (h3 : (3:R)≠0) (r : ℕ) {a : R} (ha : IsUnit a) (b : R) :
    (Finset.univ.filter (fun x : R ⧸ maximalIdeal R^r =>
      IsUnit x ∧ 3*Ideal.Quotient.mk _ a*x^2+Ideal.Quotient.mk _ b=0)).card ≤
      Nat.card (ResidueField R)^(powerDerivativeOrder R 3+powerLocalPrecision R 2) := by
  by_cases hr : powerDerivativeOrder R 3≤r
  · have he : r-powerDerivativeOrder R 3+powerDerivativeOrder R 3=r := Nat.sub_add_cancel hr
    have h := cubic_critical_unit_count_at_offset h2 h3 (r-powerDerivativeOrder R 3) (a:=a)
    rw [he] at h
    exact h ha b
  · calc
      _ ≤ Fintype.card (R ⧸ maximalIdeal R^r) := Finset.card_le_card (Finset.filter_subset _ _)
      _ = Nat.card (ResidueField R)^r := by rw [← Nat.card_eq_fintype_card,dvr_power_quotient_card]
      _ ≤ _ := Nat.pow_le_pow_right Nat.card_pos (by omega)
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.cubic_critical_unit_count_uniform
