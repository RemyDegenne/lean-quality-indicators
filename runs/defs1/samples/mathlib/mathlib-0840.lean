@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ComposableArrows

section HasZeroMorphisms

namespace IsComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] {n : ℕ} {S : ComposableArrows C (n + 3)}
  (hS : S.IsComplex) (k : ℕ)

section

/-- If `S` is a complex, this is the morphism from a cokernel of `S.map' k (k + 1)`
to a kernel of `S.map' (k + 2) (k + 3)`. -/
def cokerToKer' (hk : k ≤ n) (cc : CokernelCofork (S.map' k (k + 1)))
    (kf : KernelFork (S.map' (k + 2) (k + 3))) (hcc : IsColimit cc) (hkf : IsLimit kf) :
    cc.pt ⟶ kf.pt :=
  IsColimit.desc hcc (CokernelCofork.ofπ _
    (show S.map' k (k + 1) ≫ IsLimit.lift hkf (KernelFork.ofι _ (hS.zero (k + 1))) = _ from
      Fork.IsLimit.hom_ext hkf (by simpa using hS.zero k)))

end
end IsComplex
end HasZeroMorphisms
end ComposableArrows
end CategoryTheory
end
