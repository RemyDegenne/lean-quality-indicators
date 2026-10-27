@[expose] public section

universe w' w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

namespace MonoOver

section Map

section

variable [HasPullbacks C]

/-- `map f` is left adjoint to `pullback f` when `f` is a monomorphism -/
def mapPullbackAdj (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  (Over.mapPullbackAdj f).restrictFullyFaithful (fullyFaithfulForget X) (fullyFaithfulForget Y)
    (Iso.refl _) (Iso.refl _)

end
end Map
end MonoOver
end CategoryTheory
end
end
