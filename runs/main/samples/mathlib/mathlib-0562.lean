@[expose] public section

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe v u

variable (R : Type u) [Ring R]

attribute [instance] ModuleCat.isAddCommGroup

attribute [instance 1100] ModuleCat.isModule

variable {R}

variable {X₁ X₂ : Type v}

open ModuleCat

scoped[ModuleCat] notation "↟" f:1024 => ModuleCat.ofHom f

namespace ModuleCat

section

universe u₀

section

variable {S : Type u} [CommRing S]

variable {X Y X' Y' : ModuleCat.{v} S}

theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = .of ⟨LinearEquiv.conj i.toLinearEquiv f.asHom.hom⟩ :=
  rfl

end
end
end ModuleCat
end
