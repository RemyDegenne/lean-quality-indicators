public section

namespace TauCeti.Toric

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {σ τ : PointedCone ℝ V}

namespace ToricRay

theorem eq_hullSingleton {x : V} (hx : x ≠ 0) (ρ : ToricRay (PointedCone.hull ℝ {x})) :
    ρ = hullSingleton hx :=
  SetLike.coe_injective (congrArg (fun C : PointedCone ℝ V ↦ (C : Set V))
    (ρ.toPointedCone_eq_of_hull_singleton.trans (toPointedCone_hullSingleton hx).symm))

end ToricRay
end TauCeti.Toric
end
