import Waring.EndgameCompletionSingularCoefficients

/-! # Exact Chinese remainder transport for mixed singular coefficients -/

noncomputable section
open scoped BigOperators
namespace Waring.EndgameCompletion

def crtResidueQ (q r : ℕ) (hqr : q.Coprime r) : ZMod (q*r) →+* ZMod q :=
  (RingHom.fst (ZMod q) (ZMod r)).comp (ZMod.chineseRemainder hqr).toRingHom

def crtResidueR (q r : ℕ) (hqr : q.Coprime r) : ZMod (q*r) →+* ZMod r :=
  (RingHom.snd (ZMod q) (ZMod r)).comp (ZMod.chineseRemainder hqr).toRingHom

theorem crtResidueQ_eq_val (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (a : ZMod (q*r)) :
    crtResidueQ q r hqr a=(a.val : ZMod q) := by
  change (ZMod.cast a : ZMod q × ZMod r).1=_
  rw [Prod.fst_zmod_cast,ZMod.cast_eq_val]

theorem crtResidueR_eq_val (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (a : ZMod (q*r)) :
    crtResidueR q r hqr a=(a.val : ZMod r) := by
  change (ZMod.cast a : ZMod q × ZMod r).2=_
  rw [Prod.snd_zmod_cast,ZMod.cast_eq_val]

theorem crtResidueQ_lift (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (x : ZMod q × ZMod r) :
    crtResidueQ q r hqr (coprimeResidueLift q r x)=(r : ZMod q)*x.1 := by
  simp only [coprimeResidueLift,map_add,map_mul,map_natCast,
    ZMod.natCast_zmod_val,ZMod.natCast_self,zero_mul,add_zero]

theorem crtResidueR_lift (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (x : ZMod q × ZMod r) :
    crtResidueR q r hqr (coprimeResidueLift q r x)=(q : ZMod r)*x.2 := by
  simp only [coprimeResidueLift,map_add,map_mul,map_natCast,
    ZMod.natCast_zmod_val,ZMod.natCast_self,zero_mul,zero_add]

theorem stdAddChar_coprime (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (a : ZMod (q*r)) :
    ZMod.stdAddChar a=
      ZMod.stdAddChar (crtResidueQ q r hqr a*(↑((ZMod.unitOfCoprime r hqr.symm)⁻¹) : ZMod q))*
      ZMod.stdAddChar (crtResidueR q r hqr a*(↑((ZMod.unitOfCoprime q hqr)⁻¹) : ZMod r)) := by
  obtain ⟨x,rfl⟩ := (coprimeResidueLift_bijective q r hqr).surjective a
  rw [crtResidueQ_lift,crtResidueR_lift]
  have hqinv : (r : ZMod q)*(↑((ZMod.unitOfCoprime r hqr.symm)⁻¹) : ZMod q)=1 := by
    rw [← ZMod.coe_unitOfCoprime r hqr.symm]
    exact Units.mul_inv _
  have hrinv : (q : ZMod r)*(↑((ZMod.unitOfCoprime q hqr)⁻¹) : ZMod r)=1 := by
    rw [← ZMod.coe_unitOfCoprime q hqr]
    exact Units.mul_inv _
  rw [mul_right_comm (r : ZMod q),hqinv,one_mul,
    mul_right_comm (q : ZMod r),hrinv,one_mul]
  rw [coprimeResidueLift,AddChar.map_add_eq_mul]
  have hqchar := stdAddChar_mul_modulus q r (x.1.val : ℤ)
  have hrchar := stdAddChar_mul_modulus_left q r (x.2.val : ℤ)
  simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using congrArg₂ (fun z w : ℂ=>z*w) hqchar hrchar

theorem crt_sum_factor (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (F : ZMod q→ℂ) (G : ZMod r→ℂ) :
    (∑ x : ZMod (q*r),F (crtResidueQ q r hqr x)*G (crtResidueR q r hqr x))=
      (∑ x : ZMod q,F x)*(∑ y : ZMod r,G y) := by
  calc
    _ = ∑ z : ZMod q × ZMod r,F z.1*G z.2 := by
      exact Fintype.sum_equiv (ZMod.chineseRemainder hqr).toEquiv _ _ (fun _=>rfl)
    _ = _ := by rw [Fintype.sum_prod_type,Fintype.sum_mul_sum]

theorem productCompleteSum_coprime (q r k L : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (a : ZMod (q*r)) :
    productCompleteSum (q*r) k L a=
      productCompleteSum q k L (crtResidueQ q r hqr a*(↑((ZMod.unitOfCoprime r hqr.symm)⁻¹) : ZMod q))*
      productCompleteSum r k L (crtResidueR q r hqr a*(↑((ZMod.unitOfCoprime q hqr)⁻¹) : ZMod r)) := by
  induction L generalizing a with
  | zero => simp only [productCompleteSum_zero]; exact stdAddChar_coprime q r hqr a
  | succ L ih =>
      rw [productCompleteSum_succ,productCompleteSum_succ,productCompleteSum_succ]
      simp_rw [ih,map_mul,map_pow]
      simpa only [mul_right_comm] using crt_sum_factor q r hqr
        (fun x=>productCompleteSum q k L
          ((crtResidueQ q r hqr a*(↑((ZMod.unitOfCoprime r hqr.symm)⁻¹) : ZMod q))*x^k))
        (fun y=>productCompleteSum r k L
          ((crtResidueR q r hqr a*(↑((ZMod.unitOfCoprime q hqr)⁻¹) : ZMod r))*y^k))

theorem productCompleteMean_coprime (q r k L : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (a : ZMod (q*r)) :
    productCompleteMean (q*r) k L a=
      productCompleteMean q k L (crtResidueQ q r hqr a*(↑((ZMod.unitOfCoprime r hqr.symm)⁻¹) : ZMod q))*
      productCompleteMean r k L (crtResidueR q r hqr a*(↑((ZMod.unitOfCoprime q hqr)⁻¹) : ZMod r)) := by
  rw [productCompleteMean,productCompleteSum_coprime q r k L hqr a,
    Nat.cast_mul,mul_pow,mul_div_mul_comm]
  rfl

theorem ordinaryCompleteMean_coprime (q r k : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (a : ZMod (q*r)) :
    ordinaryCompleteMean (q*r) k a=
      ordinaryCompleteMean q k (crtResidueQ q r hqr a*(↑((ZMod.unitOfCoprime r hqr.symm)⁻¹) : ZMod q))*
      ordinaryCompleteMean r k (crtResidueR q r hqr a*(↑((ZMod.unitOfCoprime q hqr)⁻¹) : ZMod r)) := by
  simpa only [productCompleteMean,productCompleteSum_one,pow_one,ordinaryCompleteMean] using
    productCompleteMean_coprime q r k 1 hqr a

def productSingularTerm (q k u v L : ℕ) [NeZero q] (n : ℤ) (a : ZMod q) : ℂ :=
  ordinaryCompleteMean q k a^u*productCompleteMean q k L a^v*
    ZMod.stdAddChar (-a*(n : ZMod q))

theorem productSingularTerm_coprime (q r k u v L : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (n : ℤ) (a : ZMod (q*r)) :
    productSingularTerm (q*r) k u v L n a=
      productSingularTerm q k u v L n
        (crtResidueQ q r hqr a*(↑((ZMod.unitOfCoprime r hqr.symm)⁻¹) : ZMod q))*
      productSingularTerm r k u v L n
        (crtResidueR q r hqr a*(↑((ZMod.unitOfCoprime q hqr)⁻¹) : ZMod r)) := by
  unfold productSingularTerm
  rw [ordinaryCompleteMean_coprime q r k hqr,
    productCompleteMean_coprime q r k L hqr,stdAddChar_coprime q r hqr]
  simp only [map_mul,map_neg,map_intCast,mul_pow]
  have hqphase : -(crtResidueQ q r hqr a)*(n : ZMod q)*
      (↑((ZMod.unitOfCoprime r hqr.symm)⁻¹) : ZMod q)=
      -(crtResidueQ q r hqr a*(↑((ZMod.unitOfCoprime r hqr.symm)⁻¹) : ZMod q))*n := by ring
  have hrphase : -(crtResidueR q r hqr a)*(n : ZMod r)*
      (↑((ZMod.unitOfCoprime q hqr)⁻¹) : ZMod r)=
      -(crtResidueR q r hqr a*(↑((ZMod.unitOfCoprime q hqr)⁻¹) : ZMod r))*n := by ring
  rw [hqphase,hrphase]
  ring

def crtCoefficientUnits (q r : ℕ) (hqr : q.Coprime r) :
    (ZMod (q*r))ˣ ≃ (ZMod q)ˣ × (ZMod r)ˣ :=
  (coprimeUnitsEquiv q r hqr).trans
    (Equiv.prodCongr (Equiv.mulRight ((ZMod.unitOfCoprime r hqr.symm)⁻¹))
      (Equiv.mulRight ((ZMod.unitOfCoprime q hqr)⁻¹)))

theorem crtCoefficientUnits_fst (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (a : (ZMod (q*r))ˣ) :
    ((crtCoefficientUnits q r hqr a).1 : ZMod q)=
      crtResidueQ q r hqr a*(↑((ZMod.unitOfCoprime r hqr.symm)⁻¹) : ZMod q) := by
  change (↑((coprimeUnitsEquiv q r hqr a).1*(ZMod.unitOfCoprime r hqr.symm)⁻¹) : ZMod q)=_
  rw [Units.val_mul,coprimeUnitsEquiv_fst,crtResidueQ_eq_val]

theorem crtCoefficientUnits_snd (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (a : (ZMod (q*r))ˣ) :
    ((crtCoefficientUnits q r hqr a).2 : ZMod r)=
      crtResidueR q r hqr a*(↑((ZMod.unitOfCoprime q hqr)⁻¹) : ZMod r) := by
  change (↑((coprimeUnitsEquiv q r hqr a).2*(ZMod.unitOfCoprime q hqr)⁻¹) : ZMod r)=_
  rw [Units.val_mul,coprimeUnitsEquiv_snd,crtResidueR_eq_val]

/-- The literal mixed primitive singular coefficients are multiplicative. -/
theorem productSingularCoefficient_coprime (q r k u v L : ℕ) [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (n : ℤ) :
    productSingularCoefficient k u v L n (q*r)=
      productSingularCoefficient k u v L n q*productSingularCoefficient k u v L n r := by
  simp only [productSingularCoefficient_nezero]
  change (∑ a : (ZMod (q*r))ˣ,productSingularTerm (q*r) k u v L n a)=
    (∑ a : (ZMod q)ˣ,productSingularTerm q k u v L n a)*
    (∑ a : (ZMod r)ˣ,productSingularTerm r k u v L n a)
  calc
    _ = ∑ z : (ZMod q)ˣ × (ZMod r)ˣ,
        productSingularTerm q k u v L n z.1*productSingularTerm r k u v L n z.2 := by
      apply Fintype.sum_equiv (crtCoefficientUnits q r hqr)
      intro a
      rw [crtCoefficientUnits_fst,crtCoefficientUnits_snd]
      exact productSingularTerm_coprime q r k u v L hqr n a
    _ = _ := by rw [Fintype.sum_prod_type,Fintype.sum_mul_sum]

#print axioms productCompleteSum_coprime
#print axioms productSingularCoefficient_coprime
end Waring.EndgameCompletion
