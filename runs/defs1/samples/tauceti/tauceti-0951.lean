public section

namespace TauCeti

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Congr

variable (k : Type*) [Semiring k] [Linear k C] {X X' Y Y' : C}

/-- **Conjugation by isomorphisms, as an equivalence of radicals.** -/
noncomputable def jacobsonRadicalSubmoduleCongr (e : X ≅ X') (e' : Y ≅ Y') :
    jacobsonRadicalSubmodule k X Y ≃ₗ[k] jacobsonRadicalSubmodule k X' Y' :=
  (Linear.homCongr k e e').ofSubmodules _ _ (jacobsonRadicalSubmodule_map_homCongr k e e')

end Congr
end TauCeti
end
