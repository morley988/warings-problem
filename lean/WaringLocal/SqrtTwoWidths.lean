import WaringLocal.SqrtTwoLifting
import WaringLocal.FinitePrecision

/-! Exact directed Waring widths for every sufficiently deep dyadic
power in ℤ₂[√2]. The sum convention uses distinct root slots and
allows zero roots. -/
noncomputable section
namespace WaringSiegel.SqrtTwo
open WaringLocal.FinitePrecision
open scoped Padic

private theorem half_exp (a m : Nat) : 2^(a+2)*m=2*(2^(a+1)*m) := by
  rw [show a+2=(a+1)+1 by omega,pow_succ]
  ring

private theorem unit_scale (a : Nat) : (2:R)^(a+4)=4*2^(a+2) := by
  rw [show a+4=(a+2)+2 by omega,pow_add]
  ring

private theorem scalar_pow_mul (n : ℕ) (x : A) :
    (2:A)^n*x=(⟨(2:R)^n*x.re,(2:R)^n*x.im⟩:A) := by
  have h : (2:A)^n=(algebraMap R A) ((2:R)^n) := by simp
  rw [h,QuadraticAlgebra.algebraMap_eq]
  ext <;> simp

private theorem even_div_coeff (a m j : ℕ) (x : A) (h : Even x.re)
    (hj : j≤2^(a+1)*m) :
    (2:R)^j∣(x^(2^(a+2)*m)).re ∧ (2:R)^j∣(x^(2^(a+2)*m)).im := by
  rw [half_exp]
  obtain ⟨y,hy⟩ := nonunit_even_power x h (2^(a+1)*m)
  rw [hy,scalar_pow_mul]
  exact ⟨dvd_mul_of_dvd_left (pow_dvd_pow _ hj) _,dvd_mul_of_dvd_left (pow_dvd_pow _ hj) _⟩

private theorem im_div (a m : ℕ) (hm : 0<m) (x : A) : (2:R)^(a+2)∣(x^(2^(a+2)*m)).im := by
  rcases odd_or_even x.re with hx|hx
  · obtain ⟨s,t,hs,ht⟩ := dyadic_power_shape x hx a m
    refine ⟨m*(x.re*x.im*(x.re^2+2*x.im^2))+4*t,?_⟩
    rw [ht,Nat.cast_pow,Nat.cast_ofNat]
    ring
  · have h1 : a+2≤2^(a+1) := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=a+1))
    exact (even_div_coeff a m (a+2) x hx (h1.trans (Nat.le_mul_of_pos_right _ hm))).2

theorem eligible_im_div (a m : Nat) (hm : 0<m) (z : A) (hz : z∈Eligible (2^(a+2)*m)) :
    (2:R)^(a+2)∣z.im := by
  induction hz using AddSubgroup.closure_induction with
  | mem x h => obtain ⟨y,rfl⟩ := h; exact im_div a m hm y
  | zero => exact dvd_zero _
  | add x y _ _ hx hy => exact dvd_add hx hy
  | neg x _ hx => simpa using hx

theorem positive_rep (n : Nat) (x : R) :
    ∃ l : Nat, 0<l ∧ l≤2^n ∧ ∃ s : R, x=l+(2:R)^n*s := by
  let f := (PadicInt.toZModPow n : R →+* ZMod (2^n))
  let v := (f x).val
  let l := if v=0 then 2^n else v
  have hv : (v:ZMod (2^n))=f x := ZMod.natCast_zmod_val _
  have hl : (l:ZMod (2^n))=f x := by
    dsimp [l]
    split
    · rename_i h
      rw [←hv,h,Nat.cast_zero]
      exact ZMod.natCast_self _
    · exact hv
  have he : f (x-(l:R))=0 := by rw [map_sub,map_natCast,hl,sub_self]
  obtain ⟨s,hs⟩ := dvd_of_red_zero n (x-l) he
  refine ⟨l,?_,?_,s,by linear_combination hs⟩
  · dsimp [l]; split <;> positivity
  · dsimp [l]; split
    · rfl
    · exact (ZMod.val_lt _).le

theorem assemble_units_nonunits (a m n v : ℕ) (hm : Odd m) (s t : R) :
    Primitive (2^(a+2)*m) (1+n+v) (⟨1+4*(2:R)^(a+2)*s+n+v*(2:R)^(2^(a+1)*m),
        (2:R)^(a+2)*t⟩:A) := by
  obtain ⟨y,hy,he⟩ := unit_power_coset a m hm s t
  let l := List.replicate n (1:A) ++ List.replicate v pi
  have hpi : pi^(2^(a+2)*m)=(algebraMap R A) ((2:R)^(2^(a+1)*m)) := by
    rw [half_exp,pow_mul,pi_sq]
    simp
  refine ⟨y::l,by simp [l]; omega,?_,y,List.mem_cons_self,hy⟩
  simp only [powerSum,l,List.map_cons,List.map_append,List.map_replicate,
    List.sum_cons,List.sum_append,List.sum_replicate,one_pow,nsmul_eq_mul,he,hpi]
  rw [QuadraticAlgebra.algebraMap_eq]
  ext <;> simp <;> ring

/-- In particular every eligible target is a sum of at most 4d powers
including a unit, where d=2^(a+2). -/
theorem width_upper (a m : ℕ) (hm : Odd m) (z : A) (hz : z∈Eligible (2^(a+2)*m)) :
    Primitive (2^(a+2)*m) (2^(a+4)) z := by
  have hm' : 0<m := by obtain ⟨w,h⟩ := hm; omega
  obtain ⟨t,ht⟩ := eligible_im_div a m hm' z hz
  obtain ⟨l,hl,hn,s,hs⟩ := positive_rep (a+4) z.re
  let n := l-1
  have he : n+1=l := by dsimp [n]; omega
  have hn' : (n:R)+1=l := by exact_mod_cast he
  have hval : (⟨1+4*(2:R)^(a+2)*s+n+0*2^(2^(a+1)*m),(2:R)^(a+2)*t⟩:A)=z := by
    apply QuadraticAlgebra.ext
    · change 1+4*(2:R)^(a+2)*s+n+0*2^(2^(a+1)*m)=z.re
      rw [hs,unit_scale]
      linear_combination hn'
    · exact ht.symm
  obtain ⟨xs,hxs,hys,hunit⟩ := assemble_units_nonunits a m n 0 hm s t
  exact ⟨xs,hxs.trans (by omega),by simpa only [Nat.cast_zero] using hys.trans hval,hunit⟩

private def unitCount (xs : List A) : Nat := by classical exact xs.countP (fun x => decide (IsUnit x))

private theorem red_of_dvd (n : Nat) (x : R) (h : (2:R)^n∣x) : PadicInt.toZModPow n x=0 := by
  change x∈RingHom.ker (PadicInt.toZModPow n : R →+* ZMod (2^n))
  rw [PadicInt.ker_toZModPow,Ideal.mem_span_singleton]
  exact h

private theorem list_count (a m : Nat) (hbig : a+5≤2^(a+1)*m) (xs : List A) :
    PadicInt.toZModPow (a+4) (powerSum (2^(a+2)*m) xs).re =
      (unitCount xs:ZMod (2^(a+4))) := by
  classical
  induction xs with
  | nil => simp [powerSum,unitCount]
  | cons x xs ih =>
    change PadicInt.toZModPow (a+4) ((x^(2^(a+2)*m)).re+(powerSum (2^(a+2)*m) xs).re)=_
    rw [map_add,ih]
    by_cases hx : IsUnit x
    · obtain ⟨s,t,hr,_⟩ := dyadic_power_shape x ((unit_iff_odd _).mp hx) a m
      have h0 : PadicInt.toZModPow (a+4) (4*(↑(2^(a+2):Nat):R)*s)=0 := by
        apply red_of_dvd
        rw [unit_scale,Nat.cast_pow,Nat.cast_ofNat]
        exact dvd_mul_right _ _
      rw [hr,map_add,map_one,h0,add_zero]
      simp [unitCount,hx,add_comm]
    · have he := (odd_or_even x.re).resolve_left (fun h => hx ((unit_iff_odd _).mpr h))
      have h0 := red_of_dvd _ _ (even_div_coeff a m (a+4) x he (by omega)).1
      rw [h0,zero_add]
      simp [unitCount,hx]

private theorem no_units_deep (a m : Nat) (hbig : a+5≤2^(a+1)*m) (xs : List A)
    (h : unitCount xs=0) : (2:R)^(a+5)∣(powerSum (2^(a+2)*m) xs).re := by
  classical
  induction xs with
  | nil => exact dvd_zero _
  | cons x xs ih =>
    by_cases hx : IsUnit x
    · simp [unitCount,hx] at h
    · have he := (odd_or_even x.re).resolve_left (fun h => hx ((unit_iff_odd _).mpr h))
      have hl : unitCount xs=0 := by simpa [unitCount,hx] using h
      exact dvd_add (even_div_coeff a m _ x he hbig).1 (ih hl)

/-- The rational target 2^(a+4) has no representation with fewer
roots under the deep-nonunit condition, and is always eligible. -/
theorem width_lower (a m s : ℕ) (hbig : a+5≤2^(a+1)*m) (hs : s<2^(a+4)) :
    ((2:A)^(a+4))∈Eligible (2^(a+2)*m) ∧ ¬Ordinary (2^(a+2)*m) s ((2:A)^(a+4)) := by
  have hone : (1:A)∈Eligible (2^(a+2)*m) := AddSubgroup.subset_closure ⟨1,one_pow _⟩
  have hz := (Eligible (R:=A) (2^(a+2)*m)).nsmul_mem hone (2^(a+4))
  refine ⟨by simpa using hz,?_⟩
  rintro ⟨xs,hn,he⟩
  let M := 2^(a+4)
  have hr : ((2:A)^(a+4)).re=(M:R) := by
    change ((2:A)^(a+4)).re = (↑(2^(a+4):Nat):R)
    rw [show (2:A)^(a+4)=(algebraMap R A) ((2:R)^(a+4)) by simp]
    rw [QuadraticAlgebra.algebraMap_eq]
    simp
  have hcount := list_count a m hbig xs
  rw [he,hr,map_natCast,ZMod.natCast_self] at hcount
  have hd := (ZMod.natCast_eq_zero_iff (unitCount xs) _).mp hcount.symm
  have hc : unitCount xs≤xs.length := List.countP_le_length
  have hzero : unitCount xs=0 := Nat.eq_zero_of_dvd_of_lt hd (hc.trans_lt (hn.trans_lt hs))
  have hv := no_units_deep a m hbig xs hzero
  rw [he,hr] at hv
  have he' := red_of_dvd _ _ hv
  rw [map_natCast,ZMod.natCast_eq_zero_iff] at he'
  have hm : M<2^(a+5) := by
    dsimp [M]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  exact (Nat.ne_of_gt (by dsimp [M]; positivity : 0<M)) (Nat.eq_zero_of_dvd_of_lt he' hm)

theorem large_precision (a m : Nat) (hm : Odd m) (hk : 12≤2^(a+2)*m) :
    a+5≤2^(a+1)*m := by
  have hm' : 0<m := by obtain ⟨b,h⟩ := hm; omega
  cases a with
  | zero => norm_num at hk ⊢; omega
  | succ a =>
    cases a with
    | zero => norm_num at hk ⊢; omega
    | succ b =>
      have hbase (n : Nat) : n+7≤2^(n+3) := by
        induction n with
        | zero => decide
        | succ n ih =>
          rw [show n+1+3=n+3+1 by omega,pow_succ]
          omega
      exact (hbase b).trans (Nat.le_mul_of_pos_right _ hm')

/-- Exact ordinary and primitive width in the full range k≥12,
written with its odd cofactor m and its two-part 2^(a+2). -/
theorem exact_large (a m : Nat) (hm : Odd m) (hk : 12≤2^(a+2)*m) :
    (∀ z : A, z∈Eligible (2^(a+2)*m) → Primitive (2^(a+2)*m) (2^(a+4)) z) ∧
    (∀ s : Nat, s<2^(a+4) → ∃ z : A,
      z∈Eligible (2^(a+2)*m) ∧ ¬Ordinary (2^(a+2)*m) s z) := by
  have hbig := large_precision a m hm hk
  exact ⟨width_upper a m hm,fun s hs => ⟨_,width_lower a m s hbig hs⟩⟩

#print axioms exact_large
#print axioms width_upper
#print axioms width_lower
end WaringSiegel.SqrtTwo
