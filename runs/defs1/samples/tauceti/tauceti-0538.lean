public section

open Metric Module

namespace LinearIsometryEquiv

section Seminormed

variable {R E F G : Type*} [Semiring R]

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]

variable [Module R E] [Module R F] [Module R G]

/-- A linear isometry equivalence restricts to an equivalence of the corresponding unit spheres. -/
def unitSphereEquiv (e : E ≃ₗᵢ[R] F) : sphere (0 : E) 1 ≃ sphere (0 : F) 1 :=
  e.toEquiv.subtypeEquiv fun x => (map_mem_unitSphere_iff e x).symm

end Seminormed
end LinearIsometryEquiv
end
