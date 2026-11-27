import WaringSiegel.WSL4RamanujamNumerical

/-! # A strict envelope for full geometric interpolation, including constant terms -/
namespace WaringSiegel.WSL4Local

theorem ramanujam_full_interpolation_envelope_lt (m : ℝ) (hm : 3≤m) :
    4*m*(m+1)*(m*(m+1)/2+1)*(2*m-1)+
      (m-1)*(4*m-1)*(m^2+1)+1<8*m^5 := by
  let t := m-3
  have ht : 0≤t := by dsimp [t]; linarith
  have hidentity : 8*m^5-
      (4*m*(m+1)*(m*(m+1)/2+1)*(2*m-1)+
        (m-1)*(4*m-1)*(m^2+1)+1)=
      4*t^5+50*t^4+237*t^3+506*t^2+426*t+43 := by dsimp [t]; ring
  have hpos : 0<4*t^5+50*t^4+237*t^3+506*t^2+426*t+43 := by positivity
  linarith

#print axioms ramanujam_full_interpolation_envelope_lt
end WaringSiegel.WSL4Local
