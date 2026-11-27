import WaringLinear.CubicImaginary

/-! A tangent at a nontrivial integral point of the Fermat cubic yields a
norm-bounded six-cube representation over totally imaginary number fields. -/
noncomputable section
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding
open WaringSiegel WaringSiegel.WSL2 WaringLinear.CubicArchRounding
namespace WaringLinear.CubicImaginary
variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

set_option maxHeartbeats 2000000 in
private theorem six_of_affine (p q r A B C offset : 𝓞 K)
    (hoff : Eligible 3 offset)
    (hid : ∀ y : 𝓞 K, (p*y+A)^3+(q*y+B)^3+(r*y+C)^3=offset+6*y) :
    WaringSiegelBound K 3 6 := by
  apply transport
  intro B₀ hB
  let B₁ := B₀+‖embed K offset‖
  have hB₁ : 1≤B₁ := by dsimp [B₁]; linarith [norm_nonneg (embed K offset)]
  obtain ⟨C₀,hC₀,hres⟩ := bounded_residual (K:=K) B₁ hB₁
  let f (u v : 𝓞 K) := ‖embed K u‖*C₀+‖embed K v‖
  let D := C₀+f p A+f q B+f r C
  have hf (u v : 𝓞 K) : 0≤ f u v := by dsimp [f]; positivity
  have hD : 1≤D := by dsimp [D]; linarith [hf p A,hf q B,hf r C]
  refine ⟨D,hD,?_⟩
  intro S hS ν he hn
  have he' : Eligible 3 (ν-offset) := (powerSubgroup 3).sub_mem he hoff
  have hb' : ‖embed K (ν-offset)‖ ≤ B₁*S^27 := by
    rw [map_sub]
    refine (norm_sub_le _ _).trans ?_
    have hSn : 1≤S^27 := one_le_pow₀ hS
    dsimp [B₁]
    nlinarith [mul_nonneg (norm_nonneg (embed K offset)) (sub_nonneg.mpr hSn)]
  obtain ⟨a,b,c,y,hy,ha,hb,hc,hyb⟩ := hres S hS (ν-offset) he' hb'
  let X : Fin 6 → 𝓞 K := ![a,b,c,p*y+A,q*y+B,r*y+C]
  refine ⟨X,?_,?_⟩
  · simp [X,Fin.sum_univ_succ]
    linear_combination hid y - hy
  · have hbase : C₀*S^9 ≤ D*S^9 := by
      gcongr; dsimp [D]; linarith [hf p A,hf q B,hf r C]
    have haf (u v : 𝓞 K) (hfD : f u v ≤ D) : ‖embed K (u*y+v)‖ ≤ D*S^9 := by
      rw [map_add,map_mul]
      have hSn : 1≤S^9 := one_le_pow₀ hS
      calc
        _ ≤ ‖embed K u * embed K y‖+‖embed K v‖ := norm_add_le _ _
        _ ≤ ‖embed K u‖*‖embed K y‖+‖embed K v‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ ‖embed K u‖*(C₀*S^9)+‖embed K v‖ := by gcongr
        _ ≤ f u v*S^9 := by
          dsimp [f]
          nlinarith [mul_nonneg (norm_nonneg (embed K v)) (sub_nonneg.mpr hSn)]
        _ ≤ D*S^9 := by gcongr
    have ha' := ha.trans hbase
    have hb' := hb.trans hbase
    have hc' := hc.trans hbase
    have h₁ := haf p A (by dsimp [D]; linarith [hf q B,hf r C])
    have h₂ := haf q B (by dsimp [D]; linarith [hf p A,hf r C])
    have h₃ := haf r C (by dsimp [D]; linarith [hf p A,hf q B])
    intro i
    fin_cases i <;> dsimp [X] <;> assumption

/-- An integral tangent to the Fermat cubic compresses the last four
signed cubes to three, with the uniform norm bound. -/
theorem six_cubes_of_fermat_tangent (a b c : 𝓞 K) (hF : a^3+b^3+c^3=0)
    (hdiv : a*b*c^3 ∣ 2) : WaringSiegelBound K 3 6 := by
  obtain ⟨m,hm⟩ := hdiv
  apply six_of_affine (-a*m) (-b*m) (-c*m) (b^2) (-a^2) 0 (b^6-a^6)
  · apply (powerSubgroup 3).sub_mem
    · exact AddSubgroup.subset_closure ⟨b^2,by ring⟩
    · exact AddSubgroup.subset_closure ⟨a^2,by ring⟩
  · intro y
    have identity (Z : 𝓞 K) :
        (a*Z+b^2)^3+(b*Z-a^2)^3+(c*Z)^3=b^6-a^6-3*a*b*c^3*Z := by
      linear_combination (Z^3+3*a*b*Z)*hF
    linear_combination identity (-m*y) - 3*y*hm

/-- In particular the six-cube norm bound holds over every totally imaginary
field containing a primitive ninth root of unity. -/
theorem six_cubes_of_primitive_ninth_root (ξ : 𝓞 K) (hξ : IsPrimitiveRoot ξ 9) :
    WaringSiegelBound K 3 6 := by
  have hz : ξ^3 ≠ 1 := by
    intro h
    have := hξ.dvd_of_pow_eq_one 3 h
    norm_num at this
  have hprod : (ξ^3-1)*(1+ξ^3+(ξ^2)^3)=0 := by linear_combination hξ.pow_eq_one
  have hsum := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hz)
  apply six_cubes_of_fermat_tangent 1 ξ (ξ^2)
  · simpa using hsum
  · refine ⟨2*ξ^2,?_⟩
    linear_combination -2*hξ.pow_eq_one

#print axioms six_cubes_of_fermat_tangent
#print axioms six_cubes_of_primitive_ninth_root

theorem six_cubes_of_cube_root_two (β : 𝓞 K) (hβ : β^3=2) :
    WaringSiegelBound K 3 6 := by
  apply six_cubes_of_fermat_tangent 1 1 (-β)
  · linear_combination -hβ
  · refine ⟨-1,?_⟩
    linear_combination -hβ

#print axioms six_cubes_of_cube_root_two
end WaringLinear.CubicImaginary
