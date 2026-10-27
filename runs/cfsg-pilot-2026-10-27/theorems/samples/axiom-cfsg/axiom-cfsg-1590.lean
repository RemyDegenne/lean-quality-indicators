public section

namespace CFSG.SignalizerFunctorTheorem

namespace Diagonal

variable {H : Type*} [Group H]

theorem conjHom_injective (T : Subgroup H) (g : H) : Function.Injective (conjHom T g) := by
  intro x y h
  apply Subtype.ext
  simpa using h

end Diagonal
end CFSG.SignalizerFunctorTheorem
end
