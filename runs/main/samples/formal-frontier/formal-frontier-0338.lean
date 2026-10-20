@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace TopCat

theorem isOpenCover_twoOpenCover {X : TopCat.{u}} {U V : Opens X}
    (hUV : U ⊔ V = ⊤) : IsOpenCover (twoOpenCover U V) := by
  rw [IsOpenCover]
  rw [show ⨆ b : Bool, twoOpenCover U V b = U ⊔ V by
    ext x
    simp [twoOpenCover]]
  exact hUV

end TopCat
end
end
