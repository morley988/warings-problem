import Waring.DifferenceSquaresFibers
import Waring.DivisorBound
import Mathlib.Data.Finset.Card

/-! # Sharp finite collisions for positive even quadratic and quartic phases -/
noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionEvenLowDegreePairs
open DifferenceSquaresFibers

def quadraticValue (a c z : ℤ) : ℤ:=a*z^2+c

def quarticValue (a b c z : ℤ) : ℤ:=a*z^4+b*z^2+c

def quarticLift (a b z : ℤ) : ℤ:=2*a*z^2+b

def quarticDiscriminant (a b c d e : ℤ) : ℤ:=b^2-d^2-4*a*(c-e)

def quadraticPairs (a c e : ℤ) (Z W : Finset ℤ) : Finset (ℤ×ℤ):=
  (Z×ˢW).filter (fun x=>quadraticValue a c x.1=quadraticValue a e x.2)

def quarticPairs (a b c d e : ℤ) (Z W : Finset ℤ) : Finset (ℤ×ℤ):=
  (Z×ˢW).filter (fun x=>quarticValue a b c x.1=quarticValue a d e x.2)

theorem positive_sq_injective {z w : ℤ} (hz : 0<z) (hw : 0<w) (h : z^2=w^2) : z=w := by
  rcases eq_or_eq_neg_of_sq_eq_sq z w h with hh|hh
  · exact hh
  · omega

theorem quarticLift_injective {a b z w : ℤ} (ha : 0<a) (hz : 0<z) (hw : 0<w)
    (h : quarticLift a b z=quarticLift a b w) : z=w := by
  have he : (2*a)*z^2=(2*a)*w^2:=by unfold quarticLift at h; linarith
  exact positive_sq_injective hz hw (mul_left_cancel₀ (by positivity : (2*a)≠0) he)

theorem quarticValue_injective {a b c z w : ℤ} (ha : 0<a) (hb : 0≤b)
    (hz : 0<z) (hw : 0<w) (h : quarticValue a b c z=quarticValue a b c w) : z=w := by
  have hp : 0<a*(z^2+w^2)+b:=by positivity
  have hf : (z^2-w^2)*(a*(z^2+w^2)+b)=0:=by
    calc
      _ = quarticValue a b c z-quarticValue a b c w:=by unfold quarticValue; ring
      _ = 0:=sub_eq_zero.mpr h
  have he : z^2-w^2=0:= (mul_eq_zero.mp hf).resolve_right hp.ne'
  exact positive_sq_injective hz hw (sub_eq_zero.mp he)

/-- The signed difference injects every nonzero scaled square fiber into
actual divisors of its right-hand side. -/
theorem scaled_square_pairs_card_le (S : Finset (ℤ×ℤ)) {a n : ℤ}
    (ha : a≠0) (hn : n≠0) (hS : ∀x∈S,a*(x.1^2-x.2^2)=n) :
    S.card≤2*n.natAbs.divisors.card := by
  apply (Finset.card_le_card_of_injOn (fun x : ℤ×ℤ=>x.1-x.2) ?_ ?_).trans (card_signedDivisors_le n)
  · intro x hx
    apply mem_signedDivisors hn
    rw [←hS x hx]
    exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow x.1 x.2 2) a
  · intro x hx y hy hxy
    have hx0 : x.1^2-x.2^2≠0:=by
      intro hz
      have hh:=hS x hx
      rw [hz,mul_zero] at hh
      exact hn hh.symm
    have he : y.1^2-y.2^2=x.1^2-x.2^2:=
      mul_left_cancel₀ ha ((hS y hy).trans (hS x hx).symm)
    exact pair_eq_of_difference_eq hx0 rfl he hxy

theorem quadraticPairs_unequal_card_le {a c e : ℤ} (ha : a≠0) (hne : c≠e)
    (Z W : Finset ℤ) : (quadraticPairs a c e Z W).card≤2*(e-c).natAbs.divisors.card := by
  apply scaled_square_pairs_card_le _ ha (sub_ne_zero.mpr hne.symm)
  intro x hx
  have hh:=(Finset.mem_filter.mp hx).2
  unfold quadraticValue at hh
  linarith

theorem quartic_square_identity (a b c d e z w : ℤ)
    (h : quarticValue a b c z=quarticValue a d e w) :
    (quarticLift a b z)^2-(quarticLift a d w)^2=quarticDiscriminant a b c d e := by
  calc
    _ = 4*a*(quarticValue a b c z-quarticValue a d e w)+quarticDiscriminant a b c d e:=by
      unfold quarticValue quarticLift quarticDiscriminant
      ring
    _ = _:=by rw [h,sub_self,mul_zero,zero_add]

theorem quarticPairs_discriminant_ne_card_le {a b c d e : ℤ} (ha : 0<a)
    (Z W : Finset ℤ) (hZ : ∀z∈Z,0<z) (hW : ∀w∈W,0<w)
    (hdisc : quarticDiscriminant a b c d e≠0) :
    (quarticPairs a b c d e Z W).card≤2*(quarticDiscriminant a b c d e).natAbs.divisors.card := by
  let lift : ℤ×ℤ→ℤ×ℤ:=fun x=>(quarticLift a b x.1,quarticLift a d x.2)
  have hinj : Set.InjOn lift (quarticPairs a b c d e Z W : Set (ℤ×ℤ)):=by
    intro x hx y hy he
    have hx':=Finset.mem_product.mp (Finset.mem_filter.mp hx).1
    have hy':=Finset.mem_product.mp (Finset.mem_filter.mp hy).1
    apply Prod.ext
    · exact quarticLift_injective ha (hZ _ hx'.1) (hZ _ hy'.1) (congrArg Prod.fst he)
    · exact quarticLift_injective ha (hW _ hx'.2) (hW _ hy'.2) (congrArg Prod.snd he)
  rw [←Finset.card_image_iff.mpr hinj]
  apply pair_fiber_card_le _ hdisc
  intro x hx
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
  exact quartic_square_identity _ _ _ _ _ _ _ (Finset.mem_filter.mp hy).2

theorem quarticPairs_discriminant_zero_card_le {a b c d e : ℤ} (ha : 0<a)
    (hb : 0≤b) (hd : 0≤d) (hne : ¬(b=d ∧ c=e))
    (Z W : Finset ℤ) (hZ : ∀z∈Z,0<z) (hW : ∀w∈W,0<w)
    (hdisc : quarticDiscriminant a b c d e=0) :
    (quarticPairs a b c d e Z W).card≤2*(d-b).natAbs.divisors.card := by
  have hbd : b≠d:=by
    intro he
    apply hne
    refine ⟨he,?_⟩
    unfold quarticDiscriminant at hdisc
    rw [he,sub_self,zero_sub] at hdisc
    have hce : c-e=0:=by
      have hh : 4*a*(c-e)=0:=by linarith
      exact (mul_eq_zero.mp hh).resolve_left (by positivity)
    exact sub_eq_zero.mp hce
  apply scaled_square_pairs_card_le _ (by positivity : 2*a≠0) (sub_ne_zero.mpr hbd.symm)
  intro x hx
  have hmem:=Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hz:=hZ _ hmem.1
  have hw:=hW _ hmem.2
  have hh:=quartic_square_identity a b c d e x.1 x.2 (Finset.mem_filter.mp hx).2
  rw [hdisc] at hh
  have hz' : 0<quarticLift a b x.1:=by unfold quarticLift; positivity
  have hw' : 0<quarticLift a d x.2:=by unfold quarticLift; positivity
  have he:=positive_sq_injective hz' hw' (sub_eq_zero.mp hh)
  unfold quarticLift at he
  linarith

theorem quarticPairs_equal_card_le {a b c : ℤ} (ha : 0<a) (hb : 0≤b)
    (Z W : Finset ℤ) (hZ : ∀z∈Z,0<z) (hW : ∀w∈W,0<w) :
    (quarticPairs a b c b c Z W).card≤Z.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  · intro x hx y hy he
    have hx':=Finset.mem_product.mp (Finset.mem_filter.mp hx).1
    have hy':=Finset.mem_product.mp (Finset.mem_filter.mp hy).1
    have hxx:=quarticValue_injective ha hb (hZ _ hx'.1) (hW _ hx'.2) (Finset.mem_filter.mp hx).2
    have hyy:=quarticValue_injective ha hb (hZ _ hy'.1) (hW _ hy'.2) (Finset.mem_filter.mp hy).2
    apply Prod.ext he
    exact hxx.symm.trans (he.trans hyy)

theorem quadraticPairs_equal_card_le {a c : ℤ} (ha : 0<a)
    (Z W : Finset ℤ) (hZ : ∀z∈Z,0<z) (hW : ∀w∈W,0<w) :
    (quadraticPairs a c c Z W).card≤Z.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  · intro x hx y hy he
    have diag (q : ℤ×ℤ) (hq : q∈quadraticPairs a c c Z W) : q.1=q.2:=by
      have hq':=Finset.mem_product.mp (Finset.mem_filter.mp hq).1
      have hh:=(Finset.mem_filter.mp hq).2
      unfold quadraticValue at hh
      have hs : a*q.1^2=a*q.2^2:=by linarith
      exact positive_sq_injective (hZ _ hq'.1) (hW _ hq'.2) (mul_left_cancel₀ ha.ne' hs)
    exact Prod.ext he ((diag x hx).symm.trans (he.trans (diag y hy)))

#print axioms quarticPairs_discriminant_ne_card_le
#print axioms quarticPairs_discriminant_zero_card_le
#print axioms quadraticPairs_unequal_card_le
end Waring.PolicyCompletionEvenLowDegreePairs
