@[expose] public section

universe uR uS

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS}

section PrincipalIdeal

variable [Ring R] [Ring S] (f : R →+* S) (e : R)

theorem span_subsingleton_of_map_eq_zero {e : R} (he : IsIdempotentElem e)
    (h : f e = 0) : Subsingleton (Obj f (Ideal.span {MulOpposite.op e})) :=
  ⟨fun x y ↦ (span_eq_zero_of_map_eq_zero f he h x).trans
    (span_eq_zero_of_map_eq_zero f he h y).symm⟩

end PrincipalIdeal
end ModuleCat.RightExtension
end
