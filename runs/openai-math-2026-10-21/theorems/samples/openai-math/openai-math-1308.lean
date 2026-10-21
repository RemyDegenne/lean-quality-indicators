namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v

variable {V : Type u} {E : Type v}

attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_eq_intrinsicBall_of_not_radius (G : BondGraph V E)
    (ω : Set E) (x : V) (r : ℕ) (hr : ω ∉ intrinsicRadiusEvent G x r) :
    cluster G ω x = intrinsicBall G ω x r := by
  apply Set.Subset.antisymm
  · intro y hy
    apply (intrinsicBall_iff_distance_le G ω x y r hy).mpr
    have hn : ¬ r ≤ (openSimpleGraph G ω).dist x y := fun hd => hr ⟨y,hy,hd⟩
    omega
  · rintro y ⟨l,hl,_,ho⟩
    exact hl.conn ho

end Percolation.BenjaminiSchramm
end OAI
