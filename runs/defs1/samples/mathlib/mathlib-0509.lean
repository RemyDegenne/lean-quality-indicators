@[expose] public section

universe u v

open CategoryTheory

attribute [instance] AddMagmaCat.str MagmaCat.str

attribute [instance] AddSemigrp.str Semigrp.str

variable {X Y : Type u}

/-- multiplicative equivalences between `Mul`s are the same as (isomorphic to) isomorphisms
in `MagmaCat` -/
@[to_additive
    /-- additive equivalences between `Add`s are the same
    as (isomorphic to) isomorphisms in `AddMagmaCat` -/]
def mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] :
    (X ≃* Y) ≅ (MagmaCat.of X ≅ MagmaCat.of Y) where
  hom := ↾fun e ↦ e.toMagmaCatIso
  inv := ↾fun i ↦ i.magmaCatIsoToMulEquiv

end
