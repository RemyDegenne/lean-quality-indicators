@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)

attribute [instance] IsCocartesian.toIsHomLift

/-- A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is strongly co-Cartesian if for
all morphisms `φ' : a ⟶ b'` and all diagrams of the form
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ'` lifts `f ≫ g`, there exists a lift `χ` of `g` such that `φ' = χ ≫ φ`. -/
@[stacks 02XK]
class IsStronglyCocartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property' {b' : 𝒳} (g : S ⟶ p.obj b') (φ' : a ⟶ b') [IsHomLift p (f ≫ g) φ'] :
      ∃! χ : b ⟶ b', IsHomLift p g χ ∧ φ ≫ χ = φ'

end
end CategoryTheory.Functor
end
