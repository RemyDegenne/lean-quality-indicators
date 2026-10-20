@[expose] public section

universe u v w x

open scoped Pointwise

namespace Ideal

section MapAndComap

variable {R : Type u} {S : Type v}

section Semiring

variable {F : Type*} [Semiring R] [Semiring S]

variable [FunLike F R S]

variable (f : F)

variable {I J : Ideal R} {K L : Ideal S}

variable {f}

variable (f)

variable {G : Type*} [FunLike G S R]

variable [RingHomClass F R S]

variable (I J K L)

variable {f I J K L}

variable (f I J K L)

variable {ι : Sort*}

variable {I J K L}

section Bijective

variable (hf : Function.Bijective f) {I : Ideal R} {K : Ideal S}

include hf

theorem isMaximal_map_iff_of_bijective : IsMaximal (map f I) ↔ IsMaximal I := by
  simpa only [isMaximal_def] using! (relIsoOfBijective _ hf).symm.isCoatom_iff _

end Bijective
end Semiring
end MapAndComap
end Ideal
end
