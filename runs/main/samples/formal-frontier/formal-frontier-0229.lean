@[expose] public section

open scoped Topology

universe u v

namespace CharacterModule

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A]

section Comparison

variable [CompactSpace A] [NonarchimedeanAddGroup A]

theorem openKernelEquivPontryagin_naturality {B : Type v} [AddCommGroup B]
    [TopologicalSpace B] [CompactSpace B]
    [NonarchimedeanAddGroup B] (f : A →ₜ+ B) (c : openKernel B) :
    openKernelEquivPontryagin (A := A) (openKernelRestrict f c) =
      Additive.ofMul (PontryaginDual.map f.toMultiplicative
        (Additive.toMul (openKernelEquivPontryagin (A := B) c))) := by
  exact openKernelToPontryagin_naturality f c

end Comparison
end CharacterModule
end
