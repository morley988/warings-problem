import WaringSiegel.WSL4MajorRamanujamBinomialInverse

/-! # Actual tame roots of the principal-unit factors in geometric interpolation -/
noncomputable section
open IsLocalRing
namespace WaringSiegel.WSL4
variable {A : Type*} [CommRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A]

theorem principal_unit_tame_root (n : ℕ) (hn : IsUnit (n:A))
    (q : A) (hq : residue A q=0) :
    ∃ y : A,y^n=1+q ∧ residue A y=1 ∧ IsUnit y := by
  obtain ⟨y,b,hy,hyb⟩ := unit_power_step_hensel n hn q hq 1 1 isUnit_one
  have hyr : residue A y=1 := by
    rw [hyb,map_add,map_one,map_mul,hq,zero_mul,add_zero]
  refine ⟨y,by simpa only [one_pow,mul_one] using hy,hyr,?_⟩
  apply (residue_ne_zero_iff_isUnit y).mp
  rw [hyr]
  exact one_ne_zero

theorem principal_affine_power_tame_root (n P m j : ℕ) (hn : IsUnit (n:A))
    (pi x : A) (hpi : residue A pi=0) :
    ∃ y : A,y^(n*P)=(pi^(m*j+1)*x+1)^P ∧ IsUnit y := by
  have hq : residue A (pi^(m*j+1)*x)=0 := by
    simp only [map_mul,map_pow,hpi,pow_succ,mul_zero,zero_mul]
  obtain ⟨y,hy,-,hyu⟩ := principal_unit_tame_root n hn (pi^(m*j+1)*x) hq
  refine ⟨y,?_,hyu⟩
  rw [pow_mul,hy,add_comm (1:A)]

theorem principal_affine_power_family (n P m : ℕ) (hn : IsUnit (n:A))
    (pi x : A) (hpi : residue A pi=0) :
    ∃ y : Fin (P+1) → A,∀ j,
      y j^(n*P)=(pi^(m*j.val+1)*x+1)^P ∧ IsUnit (y j) := by
  choose y hy using fun j : Fin (P+1) =>
    principal_affine_power_tame_root n P m j.val hn pi x hpi
  exact ⟨y,hy⟩

#print axioms principal_unit_tame_root
#print axioms principal_affine_power_tame_root
#print axioms principal_affine_power_family
end WaringSiegel.WSL4
