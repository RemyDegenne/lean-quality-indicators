@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b a' b' : R}
  (f : QuadraticAlgebra R a b →ₐ[R] QuadraticAlgebra R a' b')

theorem trace_algHom_omega (hf : Function.Injective f) :
    trace (f ω) = b := by
  have h := (isRegular_im_omega_iff_injective f).mpr hf
  simpa [h.right.mul_right_eq_zero_iff, sub_eq_zero] using congr(im $(smul_omega_sub_eq f))

end QuadraticAlgebra
end
