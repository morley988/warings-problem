import WaringSiegel.WSL4MajorRamanujamHenselPolynomial

/-! # Sharp one-step lifting, with actual prime-ideal congruences retained -/
noncomputable section
set_option maxHeartbeats 1500000
open Polynomial IsLocalRing
open scoped Classical
namespace WaringSiegel.WSL4
variable {A : Type*} [CommRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A]

theorem polynomial_surjective_of_reduction_linear (F : A[X]) (u : A) (hu : IsUnit u)
    (hF : F.map (residue A)=C (residue A u)*X) (c : A) :
    ∃ t : A,F.eval t=c := by
  let f := F-C c
  have hur : residue A u ≠ 0 := (residue_ne_zero_iff_isUnit u).mpr hu
  let a₀ : ResidueField A := residue A c/residue A u
  have hf : f.map (residue A)=C (residue A u)*X-C (residue A c) := by
    simp only [f,Polynomial.map_sub,map_C,hF]
  have hroot : f.eval₂ (residue A) a₀=0 := by
    rw [eval₂_eq_eval_map,hf]
    simp only [eval_sub,eval_mul,eval_C,eval_X,a₀]
    field_simp [hur]
    ring
  have hder : f.derivative.eval₂ (residue A) a₀ ≠ 0 := by
    rw [eval₂_eq_eval_map,← derivative_map,hf]
    simpa only [derivative_sub,derivative_C_mul,derivative_X,derivative_C,
      mul_one,sub_zero,eval_C] using hur
  obtain ⟨t,ht,-⟩ := WSL4Weil.local_adic_simple_root_lift f a₀ hroot hder
  exact ⟨t,sub_eq_zero.mp (by simpa only [f,eval_sub,eval_C] using ht)⟩

theorem prime_power_step_hensel (p d : ℕ) (hp : p.Prime) (hd : 1 ≤ d)
    (hdp : d+2 ≤ d*p) [CharP (ResidueField A) p]
    (z c : A) (hz : IsUnit z) :
    ∃ y b : A, y^p=z^p+(p:A)^(d+1)*c ∧ y=z+(p:A)^d*b := by
  obtain ⟨u,rfl⟩ := hz
  obtain ⟨F,hF,hmap⟩ := exists_prime_scaled_lift_polynomial p d hp hd hdp
  let c' : A := ((u⁻¹:Aˣ):A)^p*c
  obtain ⟨t,ht⟩ := integer_polynomial_surjective_of_affine_mod_prime p F 0
    (by simpa only [map_zero,C_0,add_zero] using hmap) c'
  have he := congrArg (fun f : ℤ[X] => f.eval₂ (Int.castRingHom A) t) hF
  simp only [eval₂_pow,eval₂_add,eval₂_one,eval₂_mul,eval₂_C,eval₂_X,
    Int.coe_castRingHom,Int.cast_pow,Int.cast_natCast,ht] at he
  refine ⟨(u:A)*(1+(p:A)^d*t),(u:A)*t,?_,by ring⟩
  have hcancel : (u:A)^p*((u⁻¹:Aˣ):A)^p=1 := by rw [← mul_pow]; simp
  rw [mul_pow,he]
  calc
    _ = (u:A)^p+(p:A)^(d+1)*(((u:A)^p*((u⁻¹:Aˣ):A)^p)*c) := by dsimp [c']; ring
    _ = _ := by rw [hcancel,one_mul]

theorem unit_power_step_hensel (n : ℕ) (hn : IsUnit (n:A))
    (q : A) (hq : residue A q=0) (z c : A) (hz : IsUnit z) :
    ∃ y b : A,y^n=z^n+q*c ∧ y=z+q*b := by
  obtain ⟨u,rfl⟩ := hz
  obtain ⟨G,hG⟩ := exists_binomial_quadratic_tail n
  let g : A[X] := G.map (Int.castRingHom A)
  let F : A[X] := C (n:A)*X+C q*X^2*g.comp (C q*X)
  have hmap : F.map (residue A)=C (residue A (n:A))*X := by
    simp only [F,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,map_C,map_X,hq,C_0,
      zero_mul,add_zero]
  let c' : A := ((u⁻¹:Aˣ):A)^n*c
  obtain ⟨t,ht⟩ := polynomial_surjective_of_reduction_linear F (n:A) hn hmap c'
  have heval := congrArg (fun f : ℤ[X] => f.eval₂ (Int.castRingHom A) (q*t)) hG
  simp only [eval₂_pow,eval₂_add,eval₂_one,eval₂_mul,eval₂_C,eval₂_X,
    Int.coe_castRingHom,Int.cast_natCast] at heval
  have he : (1+q*t)^n=1+q*c' := by
    calc
      _ = 1+q*F.eval t := by
        rw [heval]
        simp only [F,g,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_comp,eval_map]
        ring
      _ = _ := by rw [ht]
  refine ⟨(u:A)*(1+q*t),(u:A)*t,?_,by ring⟩
  have hcancel : (u:A)^n*((u⁻¹:Aˣ):A)^n=1 := by rw [← mul_pow]; simp
  rw [mul_pow,he]
  calc
    _ = (u:A)^n+q*(((u:A)^n*((u⁻¹:Aˣ):A)^n)*c) := by dsimp [c']; ring
    _ = _ := by rw [hcancel,one_mul]

#print axioms prime_power_step_hensel
#print axioms unit_power_step_hensel
end WaringSiegel.WSL4
