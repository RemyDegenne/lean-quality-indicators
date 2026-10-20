public section

noncomputable section

open CategoryTheory Limits Metric Topology Set

universe v u

namespace HomotopicalAlgebra.AttachCells

open TauCeti

variable {X Y : TopCat.{u}} {f : X ⟶ Y} {n : ℕ}
  (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell n) f)

theorem skeletonLT_toRelCWComplex [T2Space Y] {m : ℕ} (hm : m ≤ n) :
    letI := c.toRelativeCWComplex.toRelCWComplex
    (RelCWComplex.skeletonLT (univ : Set Y) m : Set Y) = range f :=
  c.toRelativeCWComplex.skeletonLT_toRelCWComplex_eq_range fun _ hk ↦
    c.isEmpty_toRelativeCWComplex_attachCells_ι (by omega) _

end HomotopicalAlgebra.AttachCells
end
end
