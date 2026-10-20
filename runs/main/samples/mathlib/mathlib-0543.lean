@[expose] public section

open Function

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

namespace Submonoid

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

open Set

@[to_additive]
theorem comap_comap (S : Submonoid P) (g : N →* P) (f : M →* N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

end Submonoid
end
