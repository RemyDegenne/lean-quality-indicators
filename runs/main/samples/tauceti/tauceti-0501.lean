public section

open CategoryTheory Limits TopologicalSpace Opposite _root_.Topology

open TauCeti.CategoryTheory

namespace TauCeti.Topology

universe u

noncomputable section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

@[simp]
lemma cohomologyPushforwardNatIso_hom_app (hf : IsClosedEmbedding f)
    (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) (U : Opens Y) :
    (cohomologyPushforwardNatIso f hf n U).hom.app F =
      (cohomologyPushforwardIso f hf F n U).hom :=
  (rfl)

end
end TauCeti.Topology
end
