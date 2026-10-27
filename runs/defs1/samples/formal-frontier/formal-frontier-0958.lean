@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp.FreeProduct

variable {ι : Type v} (G : ι → ProfiniteGrp.{u})

namespace AdmissibleQuotient

/-- Common refinement of two finite admissible quotients. Intersecting their
kernels preserves openness after restriction to every profinite factor. -/
def inf (U V : AdmissibleQuotient G) : AdmissibleQuotient G :=
  { toFiniteIndexNormalSubgroup :=
      U.toFiniteIndexNormalSubgroup ⊓ V.toFiniteIndexNormalSubgroup
    isOpen_comap' := fun i ↦ by
      convert (U.isOpen_comap' i).inter (V.isOpen_comap' i) using 1
      ext x
      change
        (Monoid.CoprodI.of (M := fun j ↦ G j) x ∈
            U.toFiniteIndexNormalSubgroup.toSubgroup ∧
          Monoid.CoprodI.of (M := fun j ↦ G j) x ∈
            V.toFiniteIndexNormalSubgroup.toSubgroup) ↔ _
      rfl }

end AdmissibleQuotient
end ProfiniteGrp.FreeProduct
end
