@[expose] public section

open scoped Topology

universe u v

namespace CharacterModule

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A]

section Forward

variable [IsTopologicalAddGroup A]

theorem openKernelToPontryagin_naturality {B : Type v} [AddCommGroup B]
    [TopologicalSpace B] [IsTopologicalAddGroup B]
    (f : A →ₜ+ B) (c : openKernel B) :
    openKernelToPontryagin (openKernelRestrict f c) =
      Additive.ofMul (PontryaginDual.map f.toMultiplicative
        (Additive.toMul (openKernelToPontryagin c))) := by
  apply PontryaginDual.ext
  intro a
  rfl

end Forward
end CharacterModule
end
