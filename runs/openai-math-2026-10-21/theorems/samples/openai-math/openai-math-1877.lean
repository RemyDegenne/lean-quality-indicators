namespace OAI

noncomputable section

open scoped BigOperators Topology

open Finset Set Filter MeasureTheory

noncomputable section

open scoped BigOperators Topology

open Set Filter

noncomputable section

open scoped BigOperators

open Set Filter

namespace KServer.SideSupported

open Finset

variable {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] in
lemma restrict_extend (A : Finset J) (a : A → ℝ) : restrict A (extend A a)=a := by
  funext i; exact extend_apply_mem A a i

end KServer.SideSupported
end
end
end
end OAI
