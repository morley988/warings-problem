import WaringSiegel.WSL4ArchRamanujamQuotient
import WaringSiegel.WSL2LocalCount

/-! # Finite truncated-power quotients with an explicit p-power exponent

After also quotienting by p^t, the additive exponent divides p^t while
the cardinality retains the same bound from s+1 residue coordinates.
-/
noncomputable section
open IsLocalRing
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1000000
variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

def ramanujamPrecisionIdeal (p s t : ℕ) [Fact p.Prime] (I : Ideal R) :
    Ideal (ramanujamPowerSubring p s R) :=
  ramanujamPowerIdeal p s I ⊔
    Ideal.span ({((p^t:ℕ):ramanujamPowerSubring p s R)} : Set (ramanujamPowerSubring p s R))

def ramanujamPrecisionReduction (p s t : ℕ) [Fact p.Prime] (I : Ideal R) :
    ((ramanujamPowerSubring p s R) ⧸ ramanujamPowerIdeal p s I) →+*
      ((ramanujamPowerSubring p s R) ⧸ ramanujamPrecisionIdeal p s t I) :=
  Ideal.quotientMap (ramanujamPrecisionIdeal p s t I) (RingHom.id _)
    (by simpa only [Ideal.comap_id] using (le_sup_left : ramanujamPowerIdeal p s I≤ramanujamPrecisionIdeal p s t I))

theorem ramanujamPrecisionReduction_surjective (s t : ℕ) (I : Ideal R) :
    Function.Surjective (ramanujamPrecisionReduction p s t I) :=
  Ideal.quotientMap_surjective Function.surjective_id

theorem finite_ramanujamPrecisionQuotient (s t : ℕ) (I : Ideal R) [Finite (R ⧸ I)] :
    Finite ((ramanujamPowerSubring p s R) ⧸ ramanujamPrecisionIdeal p s t I) := by
  letI := finite_ramanujamPowerQuotient (p:=p) s I
  exact Finite.of_surjective _ (ramanujamPrecisionReduction_surjective (p:=p) s t I)

theorem card_ramanujamPrecisionQuotient_le (s t : ℕ) (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card ((ramanujamPowerSubring p s R) ⧸ ramanujamPrecisionIdeal p s t I)≤
      Nat.card (R ⧸ I)^(s+1) := by
  letI := finite_ramanujamPowerQuotient (p:=p) s I
  exact (Nat.card_le_card_of_surjective (ramanujamPrecisionReduction p s t I)
    (ramanujamPrecisionReduction_surjective (p:=p) s t I)).trans
      (card_ramanujamPowerQuotient_le (p:=p) s I)

theorem ramanujamPrecisionQuotient_annihilated (s t : ℕ) (I : Ideal R)
    (x : (ramanujamPowerSubring p s R) ⧸ ramanujamPrecisionIdeal p s t I) :
    (p^t) • x=0 := by
  have hm : ((p^t:ℕ):ramanujamPowerSubring p s R)∈ramanujamPrecisionIdeal p s t I :=
    (show Ideal.span ({((p^t:ℕ):ramanujamPowerSubring p s R)} : Set (ramanujamPowerSubring p s R))≤
      ramanujamPrecisionIdeal p s t I from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton _))
  have hz : ((p^t:ℕ):((ramanujamPowerSubring p s R) ⧸ ramanujamPrecisionIdeal p s t I))=0 := by
    simpa only [map_natCast] using (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
  rw [nsmul_eq_mul,hz,zero_mul]

theorem dvr_ramanujamPrecisionQuotient_card_le
    [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)]
    (s t Y f : ℕ) (hres : Nat.card (ResidueField R)=p^f) :
    Nat.card ((ramanujamPowerSubring p s R) ⧸
      ramanujamPrecisionIdeal p s t (maximalIdeal R^Y))≤p^((s+1)*(Y*f)) := by
  letI := dvr_power_quotient_finite (R:=R) Y
  calc
    _≤Nat.card (R ⧸ maximalIdeal R^Y)^(s+1) :=
      card_ramanujamPrecisionQuotient_le (p:=p) s t (maximalIdeal R^Y)
    _=p^((s+1)*(Y*f)) := by
      rw [dvr_power_quotient_card,hres,← pow_mul,← pow_mul]
      congr 1
      ring

#print axioms finite_ramanujamPrecisionQuotient
#print axioms ramanujamPrecisionQuotient_annihilated
#print axioms dvr_ramanujamPrecisionQuotient_card_le
end WaringSiegel.WSL4
