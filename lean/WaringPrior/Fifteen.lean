import WaringPrior.Primitive
import WaringSiegel.WSL4MajorRamanujamHenselTuple

noncomputable section
open scoped NumberField
open IsLocalRing WaringSiegel.WSL4
namespace WaringSmallK.Local

variable {A : Type*} [CommRing A] [Nontrivial A] [IsLocalRing A]
    [Finite (ResidueField A)] [CharP (ResidueField A) 2]

/-- Three fourth powers, at least one a unit, give every residue modulo four
if the unramified dyadic ring contains a primitive cube root of unity. -/
theorem three_digits (he : maximalIdeal A = Ideal.span {(2:A)})
    (u : A) (hu : u^2+u+1=0) (a : A) :
    ∃ w x y c : A, IsUnit w ∧ a=w^4+x^4+y^4+4*c := by
  obtain ⟨w,b,hw⟩ := fourth_digit he a
  obtain ⟨x,c,hx⟩ := fourth_digit he b
  by_cases hwu : IsUnit w
  · exact ⟨w,x,x,c,hwu,by linear_combination hw + 2*hx⟩
  by_cases hxu : IsUnit x
  · exact ⟨x,w,x,c,hxu,by linear_combination hw + 2*hx⟩
  have hd (t : A) (h : ¬ IsUnit t) : (2:A) ∣ t := by
    have hm : t ∈ maximalIdeal A := h
    rw [he,Ideal.mem_span_singleton] at hm
    exact hm
  obtain ⟨v,hv⟩ := hd w hwu
  obtain ⟨z,hz⟩ := hd x hxu
  have hu3 : u^3=1 := by linear_combination (u-1)*hu
  have hu4 : u^4=u := by linear_combination u*hu3
  refine ⟨1,u,u^2,4*v^4+8*z^4+c,isUnit_one,?_⟩
  rw [show (u^2)^4=(u^4)^2 by ring,hu4,one_pow,hw,hx,hv,hz]
  linear_combination -hu

theorem unramified_quartic_fifteen_tuple [IsAdicComplete (maximalIdeal A) A]
    (he : maximalIdeal A = Ideal.span {(2:A)}) (u : A) (hu : u^2+u+1=0) (a : A) :
    ∃ x : Fin 15 → A, (∑ i, (x i)^4)=a ∧ ∃ i,IsUnit (x i) := by
  obtain ⟨w,x,y,c,hw,ha⟩ := three_digits he u hu a
  obtain ⟨z,d,hz⟩ := fourth_digit he c
  obtain ⟨v,e,hv⟩ := fourth_digit he d
  let l := [w,x,y,z,z,z,z,v,v,v,v,v,v,v,v]
  let t : Fin 15 → A := l.get
  have hmod : (2:A)^4 ∣ a-∑ i, (t i)^4 := by
    refine ⟨e,?_⟩
    change a-(∑ i : Fin l.length, (l.get i)^4)=_
    rw [sum_power_get_eq_localPowerListSum]
    simp only [l,localPowerListSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    linear_combination ha + 4*hz + 8*hv
  exact power_tuple_lift_sharp_of_not_dvd 2 1 2 (by decide) (by decide) t a ⟨0,hw⟩ hmod

theorem fifteen_of_largeK (hA : WaringSiegel.LargeKAnalyticClaim)
    (K : Type) [Field K] [NumberField K] (he : UnramifiedAtTwo K)
    (hu : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ¬IsUnit (4:v.adicCompletionIntegers K) →
      ∃ u : v.adicCompletionIntegers K, u^2+u+1=0) :
    WaringSiegel.WaringSiegelBound K 4 15 := by
  apply WaringSiegel.bound_of_localConditionalBound (hA K 4 15 (by decide) ?_)
  · intro a ha v
    by_cases h4 : IsUnit (4:v.adicCompletionIntegers K)
    · exact power_tuple_with_unit_mono 4 (by decide)
        (power_tuple_in_completion_of_unit v 4 (by decide) h4 ha) (by decide)
    · let A := v.adicCompletionIntegers K
      have h2 : ¬IsUnit (2:A) := fun h => h4 (by convert h.mul h using 1; norm_num)
      letI := residue_charP_of_prime_not_isUnit 2 (by decide) h2
      letI := WaringSiegel.completionIntegers_residueFinite v
      letI := WaringSiegel.completionIntegers_isAdicComplete v
      obtain ⟨u,hur⟩ := hu v h4
      exact unramified_quartic_fifteen_tuple (he v h4) u hur _
  · rw [WaringSiegel.Thresholds.variables_4]; decide

end WaringSmallK.Local
#print axioms WaringSmallK.Local.fifteen_of_largeK
