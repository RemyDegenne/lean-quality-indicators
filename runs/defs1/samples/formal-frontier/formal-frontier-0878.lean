@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp.FreeProduct

variable {ι : Type v} (G : ι → ProfiniteGrp.{u})

/-- The abstract free product of the underlying groups. -/
abbrev Abstract : Type max u v :=
  @Monoid.CoprodI.{v, u} ι (fun i ↦ G i) (fun i ↦ (G i).group.toMonoid)

end ProfiniteGrp.FreeProduct
end
