@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp.FreeProduct

variable {ι : Type v} (G : ι → ProfiniteGrp.{u})

/-- A finite quotient of the abstract free product is admissible when its
restriction to every profinite factor is continuous. Openness of the kernels
is the convenient finite-discrete formulation of this condition. -/
@[ext]
structure AdmissibleQuotient extends FiniteIndexNormalSubgroup (Abstract G) where
  isOpen_comap' (i : ι) : IsOpen
    (((toFiniteIndexNormalSubgroup.toSubgroup.comap
      (Monoid.CoprodI.of (M := fun j ↦ G j) : G i →* Abstract G)) :
        Subgroup (G i)) : Set (G i))

end ProfiniteGrp.FreeProduct
end
