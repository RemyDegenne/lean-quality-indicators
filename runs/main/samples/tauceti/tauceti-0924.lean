public section

open CategoryTheory

open scoped Pointwise

universe u v w

namespace TauCeti

variable {k : Type u} {G : Type v} [Group G]

section FDRepFinrank

variable [Ring k]

@[simp]
theorem finrank_conjFDRep (s : G) {H : Subgroup G} (A : FDRep k H) :
    Module.finrank k (conjFDRep s A).V = Module.finrank k A.V :=
  congrArg (fun V : FGModuleCat k => Module.finrank k V) (conjFDRep_V s A)

end FDRepFinrank
end TauCeti
end
