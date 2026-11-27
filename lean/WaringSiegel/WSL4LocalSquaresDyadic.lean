import WaringSiegel.WSL4LocalSquaresHensel

/-! # Five local squares with a unit in arbitrary residue characteristic two -/
noncomputable section
set_option maxHeartbeats 1400000
open IsLocalRing
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
variable {R : Type*} [CommRing R] [HenselianLocalRing R]

theorem five_squares_henselian_two_nonunit (h2:¬IsUnit (2:R))
    {a:R} (ha:a∈squareSpan R) :
    ∃y:Fin 5→R,(∑i,y i^2)=a ∧ ∃i,IsUnit (y i) := by
  obtain ⟨x,u,ha⟩ := squareSpan_le_squareModTwo ha
  obtain ⟨r,hr,hres⟩ := dyadic_hensel_minus_seven h2
  have hru : IsUnit r := (residue_ne_zero_iff_isUnit r).mp (by rw [hres]; exact neg_ne_zero.mpr one_ne_zero)
  have h20 : (2:ResidueField R)=0 := by
    have hh := (residue_ne_zero_iff_isUnit (2:R)).not.mpr h2
    simpa only [map_ofNat,not_not] using hh
  by_cases hxu : IsUnit x
  · obtain ⟨d,hd⟩ := isUnit_iff_exists_inv.mp (hru.mul hxu)
    let t := u*d
    have he : 2*(r*x+3*(0:R))*t=a-(x^2+2*(0:R)) := by
      calc
        _ = 2*u*((r*x)*d) := by dsimp [t]; ring
        _ = _ := by rw [hd,ha]; ring
    let y : Fin 5→R := ![x+t*r,2*t,t,t,t]
    refine ⟨y,?_,?_⟩
    · have hs := dyadic_five_square_identity a x 0 r t hr (by ring) he
      simpa [y,Fin.sum_univ_succ,add_assoc] using hs
    · by_cases htu : IsUnit t
      · exact ⟨3,by simpa [y] using htu⟩
      · refine ⟨0,?_⟩
        change IsUnit (x+t*r)
        apply (residue_ne_zero_iff_isUnit _).mp
        have ht0 : residue R t=0 := by
          simpa only [not_not] using (residue_ne_zero_iff_isUnit t).not.mpr htu
        simpa only [map_add,map_mul,ht0,zero_mul,add_zero] using
          (residue_ne_zero_iff_isUnit x).mpr hxu
  · have hx0 : residue R x=0 := by
      simpa only [not_not] using (residue_ne_zero_iff_isUnit x).not.mpr hxu
    have hb : IsUnit (r*x+3) := by
      apply (residue_ne_zero_iff_isUnit _).mp
      have h3 : (3:ResidueField R)=1 := by
        calc
          (3:ResidueField R)=2+1 := by ring
          _ = 1 := by rw [h20,zero_add]
      simp only [map_add,map_mul,map_ofNat,hx0,mul_zero,zero_add,h3,ne_eq,one_ne_zero,not_false_eq_true]
    obtain ⟨d,hd⟩ := isUnit_iff_exists_inv.mp hb
    let t := (u-1)*d
    have he : 2*(r*x+3*(1:R))*t=a-(x^2+2*(1:R)) := by
      calc
        _ = 2*(u-1)*((r*x+3)*d) := by dsimp [t]; ring
        _ = _ := by rw [hd,ha]; ring
    let y : Fin 5→R := ![x+t*r,1+2*t,1+t,t,t]
    refine ⟨y,?_,1,?_⟩
    · have hs := dyadic_five_square_identity a x 1 r t hr (by ring) he
      simpa [y,Fin.sum_univ_succ,add_assoc] using hs
    · change IsUnit (1+2*t)
      apply (residue_ne_zero_iff_isUnit _).mp
      simp only [map_add,map_one,map_mul,map_ofNat,h20,zero_mul,add_zero,ne_eq,one_ne_zero,not_false_eq_true]

theorem five_squares_henselian_finite_residue [Finite (ResidueField R)]
    {a:R} (ha:a∈squareSpan R) :
    ∃y:Fin 5→R,(∑i,y i^2)=a ∧ ∃i,IsUnit (y i) := by
  by_cases h2:IsUnit (2:R)
  · exact five_squares_henselian_two_unit h2 a
  · exact five_squares_henselian_two_nonunit h2 ha

#print axioms five_squares_henselian_two_nonunit
#print axioms five_squares_henselian_finite_residue
end WaringSiegel.WSL4Local
