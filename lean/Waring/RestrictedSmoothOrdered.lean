import Waring.RestrictedSmoothFactorization

/-!
# Uniqueness of the ordered smooth-factor window

The window factor has all prime factors at least pi, the complementary
factor has all prime factors at most pi, and M<m<=M*pi. These conditions
select exactly one factorization. This is the literal ordered decomposition
used in the restricted smooth-mean argument.
-/

noncomputable section
namespace Waring.RestrictedSmoothFactorization
open SmoothMoments

def OrderedWindow (M : ℝ) (π m w : ℕ) : Prop :=
  π.Prime ∧ π ∣ m ∧ 0 < w ∧ M < (m : ℝ) ∧ (m : ℝ) ≤ M*(π : ℝ) ∧
    PrimeRestricted (fun p => π ≤ p) m ∧ IsSmooth w (π : ℝ)

theorem orderedWindow_m_pos {M : ℝ} (hM : 1 ≤ M) {π m w : ℕ}
    (h : OrderedWindow M π m w) : 0 < m := by
  exact_mod_cast (zero_lt_one.trans_le hM |>.trans h.2.2.2.1)

theorem exists_orderedWindow (n : ℕ) {M : ℝ} (hM : 1 ≤ M) (hnM : M < (n : ℝ)) :
    ∃ π m w : ℕ, n=m*w ∧ OrderedWindow M π m w := by
  obtain ⟨π,m,w,hπ,hn,hπm,hMm,hmM,hrough,hsmooth⟩ := exists_ordered_window n hM hnM
  have hw : 0 < w := by
    by_contra h
    have hw0 : w=0 := by omega
    simp only [hw0,mul_zero] at hn
    subst n
    norm_num at hnM
    linarith
  exact ⟨π,m,w,hn,hπ,hπm,hw,hMm,hmM,hrough,hsmooth⟩

private theorem ordered_threshold_not_lt {M : ℝ} (hM : 1 ≤ M)
    {π m w π' m' w' : ℕ} (h : OrderedWindow M π m w)
    (h' : OrderedWindow M π' m' w') (heq : m*w=m'*w') : ¬π < π' := by
  intro hlt
  have hcop : m'.Coprime w := by
    apply Nat.coprime_of_dvd
    intro p hp hpm hpw
    have hlo := h'.2.2.2.2.2.1 p hp hpm
    have hhi : p ≤ π := by exact_mod_cast h.2.2.2.2.2.2 p hp hpw
    omega
  have hmdiv : m' ∣ m := hcop.dvd_of_dvd_mul_right (by rw [heq]; exact dvd_mul_right m' w')
  obtain ⟨c,hmc⟩ := hmdiv
  have hcpos : 0 < c := by
    have hmp := orderedWindow_m_pos hM h
    by_contra hc
    have hc0 : c=0 := by omega
    simp only [hc0,mul_zero] at hmc
    omega
  have hnot : ¬π ∣ m' := by
    intro hd
    have hh := h'.2.2.2.2.2.1 π h.1 hd
    omega
  have hπc : π ∣ c := (h.1.dvd_mul.mp (hmc ▸ h.2.1)).resolve_left hnot
  have hπcR : (π : ℝ) ≤ c := by exact_mod_cast Nat.le_of_dvd hcpos hπc
  have hπp : 0 < (π : ℝ) := by exact_mod_cast h.1.pos
  have hstrict := mul_lt_mul_of_pos_right h'.2.2.2.1 hπp
  have hle := mul_le_mul_of_nonneg_left hπcR (by positivity : 0 ≤ (m' : ℝ))
  have hmcR : (m : ℝ)=(m' : ℝ)*(c : ℝ) := by exact_mod_cast hmc
  linarith [h.2.2.2.2.1]

private theorem rough_divides_of_factorization_le {π m w m' w' : ℕ}
    (hm : 0 < m) (hw : 0 < w) (hm' : 0 < m') (hw' : 0 < w')
    (heq : m*w=m'*w')
    (hrough : PrimeRestricted (fun p => π ≤ p) m)
    (hsmooth : IsSmooth w (π : ℝ)) (hsmooth' : IsSmooth w' (π : ℝ))
    (hval : m.factorization π ≤ m'.factorization π) : m ∣ m' := by
  apply (Nat.factorization_le_iff_dvd hm.ne' hm'.ne').mp
  intro p
  by_cases hp : p.Prime
  · rcases lt_trichotomy p π with hlt | rfl | hgt
    · rw [Nat.factorization_eq_zero_of_not_dvd (show ¬p ∣ m by
        intro hd; exact (not_le_of_gt hlt) (hrough p hp hd))]
      exact Nat.zero_le _
    · exact hval
    · have hw0 : w.factorization p=0 := Nat.factorization_eq_zero_of_not_dvd (by
        intro hd
        have hh : p ≤ π := by exact_mod_cast hsmooth p hp hd
        omega)
      have hw'0 : w'.factorization p=0 := Nat.factorization_eq_zero_of_not_dvd (by
        intro hd
        have hh : p ≤ π := by exact_mod_cast hsmooth' p hp hd
        omega)
      have hfac := congrArg (fun n : ℕ => n.factorization p) heq
      change (m*w).factorization p=(m'*w').factorization p at hfac
      rw [Nat.factorization_mul hm.ne' hw.ne',Nat.factorization_mul hm'.ne' hw'.ne',
        Finsupp.add_apply,Finsupp.add_apply,hw0,hw'0,add_zero,add_zero] at hfac
      exact hfac.le
  · rw [Nat.factorization_eq_zero_of_non_prime _ hp]
    exact Nat.zero_le _

private theorem ordered_eq_of_dvd {M : ℝ} (hM : 1 ≤ M) {π m w m' w' : ℕ}
    (h : OrderedWindow M π m w) (h' : OrderedWindow M π m' w') (hdiv : m ∣ m') : m=m' := by
  obtain ⟨c,hmc⟩ := hdiv
  by_cases hc1 : c=1
  · simpa only [hc1,mul_one] using hmc.symm
  have hcpos : 0 < c := by
    have hmp := orderedWindow_m_pos hM h'
    by_contra hc
    have hc0 : c=0 := by omega
    simp only [hc0,mul_zero] at hmc
    omega
  obtain ⟨p,hp,hpc⟩ := Nat.exists_prime_and_dvd hc1
  have hpm' : p ∣ m' := by rw [hmc]; exact dvd_mul_of_dvd_right hpc m
  have hπp := h'.2.2.2.2.2.1 p hp hpm'
  have hπcR : (π : ℝ) ≤ c := by exact_mod_cast hπp.trans (Nat.le_of_dvd hcpos hpc)
  have hπpos : 0 < (π : ℝ) := by exact_mod_cast h.1.pos
  have hstrict := mul_lt_mul_of_pos_right h.2.2.2.1 hπpos
  have hle := mul_le_mul_of_nonneg_left hπcR (by positivity : 0 ≤ (m : ℝ))
  have hmcR : (m' : ℝ)=(m : ℝ)*(c : ℝ) := by exact_mod_cast hmc
  linarith [h'.2.2.2.2.1]

/-- No ordered factor or threshold can be counted twice. -/
theorem orderedWindow_unique {M : ℝ} (hM : 1 ≤ M) {π m w π' m' w' : ℕ}
    (h : OrderedWindow M π m w) (h' : OrderedWindow M π' m' w')
    (heq : m*w=m'*w') : π=π' ∧ m=m' ∧ w=w' := by
  have hπ : π=π' := by
    have hn := ordered_threshold_not_lt hM h h' heq
    have hn' := ordered_threshold_not_lt hM h' h heq.symm
    omega
  subst π'
  have hm := orderedWindow_m_pos hM h
  have hm' := orderedWindow_m_pos hM h'
  have hmeq : m=m' := by
    rcases le_total (m.factorization π) (m'.factorization π) with hval | hval
    · exact ordered_eq_of_dvd hM h h'
        (rough_divides_of_factorization_le hm h.2.2.1 hm' h'.2.2.1 heq
          h.2.2.2.2.2.1 h.2.2.2.2.2.2 h'.2.2.2.2.2.2 hval)
    · exact (ordered_eq_of_dvd hM h' h
        (rough_divides_of_factorization_le hm' h'.2.2.1 hm h.2.2.1 heq.symm
          h'.2.2.2.2.2.1 h'.2.2.2.2.2.2 h.2.2.2.2.2.2 hval)).symm
  refine ⟨rfl,hmeq,?_⟩
  rw [← hmeq] at heq
  exact Nat.eq_of_mul_eq_mul_left hm heq

#print axioms orderedWindow_unique
end Waring.RestrictedSmoothFactorization
