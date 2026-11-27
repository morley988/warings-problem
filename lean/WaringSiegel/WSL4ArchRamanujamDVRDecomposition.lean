import WaringSiegel.WSL4ArchRamanujamGenerators

/-! # Quantitative actual-power representatives and deep ghost remainders

This is valid for ramified discrete valuation rings. Only the residue-field
cardinality is used: no coefficient field or unramified subring is assumed.
-/
noncomputable section
open scoped BigOperators
open IsLocalRing
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1400000
variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

theorem ramanujamPrecisionIdeal_remainder (s t : ℕ) (I : Ideal R)
    (b : ramanujamPowerSubring p s R)
    (hb : b∈ramanujamPrecisionIdeal p s t I) :
    ∃w : Fin (s+1) → R,∃z : R,(∀i,w i∈I) ∧
      (b:R)=ramanujamPowerTuple p s w+(p:R)^t*z := by
  obtain ⟨u,hu,v,hv,huv⟩ := Submodule.mem_sup.mp hb
  obtain ⟨w,hw,hew⟩ := (mem_ramanujamPowerIdeal_iff_fin (p:=p) s I u).mp hu
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hv
  refine ⟨w,(z:R),hw,?_⟩
  have huvR : (u:R)+(v:R)=(b:R) := congrArg (fun x : ramanujamPowerSubring p s R => (x:R)) huv
  have hzv : (v:R)=(p:R)^t*(z:R) := by
    have hh := congrArg (ramanujamPowerSubring p s R).subtype hz
    simpa only [map_mul,map_natCast,Nat.cast_pow] using hh
  rw [← hew,hzv] at huvR
  exact huvR.symm

theorem dvr_eligible_power_list_deep_remainder
    [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)]
    (n s t Y f : ℕ) (hst : s+1≤t) (hres : Nat.card (ResidueField R)=p^f)
    (a : R) (ha : a∈AddSubgroup.closure (Set.range (fun x : R => x^(n*p^s)))) :
    ∃l : List R,∃w : Fin (s+1) → R,∃z : R,
      l.length≤Y*f*(p^t-1) ∧ (∀i,w i∈maximalIdeal R^Y) ∧
      a=localPowerListSum (n*p^s) l+ramanujamPowerTuple p s w+(p:R)^t*z := by
  let C := ramanujamPowerSubring p s R
  let I := maximalIdeal R^Y
  let J := ramanujamPrecisionIdeal p s t I
  let q := Ideal.Quotient.mk J
  let g : R → C ⧸ J := fun x => q (ramanujamPowerGenerator p n s x)
  letI := dvr_power_quotient_finite (R:=R) Y
  letI := finite_ramanujamPrecisionQuotient (p:=p) s t I
  obtain ⟨b,hba,hb⟩ := eligible_power_generator_mem_closure (p:=p) n s a ha
  have hqmem : q b∈AddSubgroup.closure (Set.range g) :=
    ramanujamPowerGenerator_quotient_mem_closure n s J b hb
  have hcard : Nat.card (C ⧸ J)≤p^((s+1)*(Y*f)) :=
    dvr_ramanujamPrecisionQuotient_card_le (p:=p) s t Y f hres
  have hexp : ∀x : C ⧸ J,(p^t) • x=0 :=
    ramanujamPrecisionQuotient_annihilated s t I
  obtain ⟨l,hl,hlen⟩ := finite_additive_image_list_count_scaled p t ((s+1)*(Y*f)) (Y*f)
    (Fact.out : p.Prime) (by omega) (Nat.mul_le_mul_right _ hst) hcard hexp g (q b) hqmem
  let lc : C := (l.map (ramanujamPowerGenerator p n s)).sum
  have hqlc : q lc=q b := by
    change q ((l.map (ramanujamPowerGenerator p n s)).sum)=q b
    rw [map_list_sum,List.map_map]
    exact hl
  have hdiff : b-lc∈J := Ideal.Quotient.eq.mp hqlc.symm
  obtain ⟨w,z,hw,he⟩ := ramanujamPrecisionIdeal_remainder s t I (b-lc) hdiff
  have hlc : (lc:R)=localPowerListSum (n*p^s) l := ramanujamPowerGenerator_list_sum n s l
  change (b:R)-(lc:R)=ramanujamPowerTuple p s w+(p:R)^t*z at he
  rw [hba,hlc] at he
  refine ⟨l,w,z,hlen,hw,?_⟩
  linear_combination he

#print axioms ramanujamPrecisionIdeal_remainder
#print axioms dvr_eligible_power_list_deep_remainder
end WaringSiegel.WSL4
