@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w

namespace CategoryTheory

open CategoryTheory.Functor Limits GrothendieckTopology

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (e : C ≌ D) (G : D ⥤ C)

variable (A : Type u₃) [Category.{v₃} A]

variable (B : Type u₄) [Category.{v₄} B] (F : A ⥤ B)

section

variable [EssentiallySmall.{w} C]

variable [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A]

variable [((equivSmallModel C).inverse.inducedTopology J).HasSheafCompose F]

/--
Transporting to a small model and sheafifying there is left adjoint to the underlying presheaf
functor
-/
noncomputable
def smallSheafificationAdjunction : smallSheafify J A ⊣ sheafToPresheaf J A :=
  (equivSmallModel C).transportSheafificationAdjunction J _ A

end
end CategoryTheory
end
