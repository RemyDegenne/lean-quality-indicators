public section

namespace TauCeti

open PathAlgebra DoubledQuiver Polynomial

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- **The graded dictionary**: the homomorphisms `P_i{d} → P_j` are the degree-`d` part of the
corner `e_i Z e_j`. -/
noncomputable def zigzagProjectiveHomOfDegreeEquivGradedCorner (i j : V) (d : ℕ) :
    zigzagProjectiveHomOfDegree k G i j d ≃ₗ[k] zigzagGradedCorner k G i j d :=
  (LinearEquiv.ofEq _ _ (zigzagProjectiveHomOfDegree_eq_comap k G i j d)).trans
    (((zigzagProjectiveHomEquivCorner k G i j).ofSubmodules _ _
        (Submodule.map_comap_eq_of_surjective
          (zigzagProjectiveHomEquivCorner k G i j).surjective _)).trans
      (Submodule.comapSubtypeEquivOfLe (zigzagGradedCorner_le_zigzagCorner k G i j d)))

end TauCeti
end
