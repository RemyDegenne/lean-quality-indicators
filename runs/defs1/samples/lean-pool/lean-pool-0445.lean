@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

open SuperCommAlgebra (pointMod)

open SuperCommAlgebra.Mod

universe u

section SuperVectUnit

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)

/-- **The unit comparison of the fibre functor**, before the
coordinates are installed: a complex number is scaled into the
algebra and pushed into the base change. -/
noncomputable def superVectEpsRaw :
    ℂ →ₗ[ℂ] ((S.unitMod : S.Mod.{u, u, u, u}).tensor
      (pointMod P)).even :=
  (pointBaseEps P).evenMap ∘ₗ
    LinearMap.toSpanSingleton ℂ S.even S.one

end SuperVectUnit
end RS
end
