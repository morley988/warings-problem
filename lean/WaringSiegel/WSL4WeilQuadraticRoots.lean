import WaringSiegel.WSL4WeilFiniteStationary
import WaringSiegel.WSL3MomentLocalPowerGood

/-! # Uniform stationary root counts over local quotients -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical
open IsLocalRing Polynomial

theorem finite_field_quadratic_zero_count
    {F : Type*} [Field F] [Fintype F] {a : F} (ha : a ≠ 0) (b : F) :
    (Finset.univ.filter (fun x : F => a*x^2+b=0)).card ≤ 2 := by
  let f : F[X] := C a*X^2+C b
  have hd : f.natDegree=2 := by
    dsimp [f]
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_C_mul_X_pow _ _ ha]
    rw [natDegree_C_mul_X_pow _ _ ha, natDegree_C]
    norm_num
  have hf : f≠0 := by intro h; simp [h] at hd
  have he : Finset.univ.filter (fun x : F => a*x^2+b=0)=f.roots.toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      mem_roots hf, IsRoot.def, f, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  rw [he]
  exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' f).trans_eq hd)

theorem quadratic_unit_roots_residue_injective
    {R : Type*} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R)
    (h2 : IsUnit (2 : R)) {a b : R} (ha : IsUnit a) (hb : IsUnit b) :
    Function.Injective (fun x : {x : R ⧸ I // Ideal.Quotient.mk I a*x^2+Ideal.Quotient.mk I b=0} =>
      localResidueReduction I hI x.val) := by
  intro x y hxy
  have hsq : x.val^2=y.val^2 := by
    apply (ha.map (Ideal.Quotient.mk I)).mul_left_cancel
    exact add_right_cancel (x.property.trans y.property.symm)
  have hx : localResidueReduction I hI x.val ≠ 0 := by
    intro hz
    have he := congrArg (localResidueReduction I hI) x.property
    simp only [map_add, map_mul, map_pow, map_zero, localResidueReduction_mk, hz,
      zero_pow (by decide : 2≠0), mul_zero, zero_add] at he
    exact ((residue_ne_zero_iff_isUnit b).mpr hb) he
  apply Subtype.ext
  exact (WSL3.power_eq_iff_of_same_nonzero_residue 2 (by decide) h2 I hI hxy hx).mp hsq

theorem quadratic_unit_roots_card_le_two
    {R : Type*} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R)
    [Fintype (R ⧸ I)] [Fintype (ResidueField R)]
    (h2 : IsUnit (2 : R)) {a b : R} (ha : IsUnit a) (hb : IsUnit b) :
    (Finset.univ.filter (fun x : R ⧸ I =>
      Ideal.Quotient.mk I a*x^2+Ideal.Quotient.mk I b=0)).card ≤ 2 := by
  let f : {x : R ⧸ I // Ideal.Quotient.mk I a*x^2+Ideal.Quotient.mk I b=0} →
      {x : ResidueField R // residue R a*x^2+residue R b=0} := fun x =>
    ⟨localResidueReduction I hI x.val, by
      simpa only [map_add, map_mul, map_pow, map_zero, localResidueReduction_mk] using
        congrArg (localResidueReduction I hI) x.property⟩
  have hi : Function.Injective f := by
    intro x y h
    exact quadratic_unit_roots_residue_injective I hI h2 ha hb (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hi
  simp only [Fintype.card_subtype] at hc
  exact hc.trans (finite_field_quadratic_zero_count
    ((residue_ne_zero_iff_isUnit a).mpr ha) (residue R b))

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.quadratic_unit_roots_card_le_two
