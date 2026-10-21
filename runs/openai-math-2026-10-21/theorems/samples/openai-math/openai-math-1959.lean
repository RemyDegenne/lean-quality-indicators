namespace OAI

noncomputable section

open Set Topology Metric

open Set Topology Metric

open scoped unitInterval

open Set Topology Metric

open scoped unitInterval

open Set Topology Metric

open scoped unitInterval

open Set Topology Metric

open scoped unitInterval

open CategoryTheory AlgebraicTopology Limits

open Set Topology

open scoped unitInterval

namespace SingularSphereCycle

open Set Topology CategoryTheory AlgebraicTopology

open scoped Simplicial

open SphereQuotient

lemma collapse_face (n : ℕ) (i : Fin (n+2)) (s : Convexity.StdSimplex ℝ (Fin (n+1))) :
    collapse (n+1) (Convexity.StdSimplex.map i.succAbove s) = pole (n+1) :=
  quotient_boundary _ (SimplexDisk.diskEquiv_boundary _ i (face_zero i s))

end SingularSphereCycle
end
end OAI
