@[expose] public section

universe u v

variable {R : Type u} {M : Type v}

open Set Function

open Submodule

namespace IsBezout

variable [CommRing R] (x y z : R) [(Ideal.span {x, y}).IsPrincipal]

theorem gcd_dvd_right : gcd x y ∣ y :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))

end IsBezout
end
