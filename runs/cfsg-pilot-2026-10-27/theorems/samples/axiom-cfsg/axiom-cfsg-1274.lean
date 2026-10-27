public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

open scoped Pointwise

universe u

variable {G : Type u} [Group G]

section Geometry

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G}

section Finite

variable [Finite G]

theorem exists_dist_eq_critB (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    ∃ μ : CosetGeom G₀ G₁ G₂, CosetGeom.dist (γ₀ G₀ G₁ G₂) μ = critB G₀ G₁ G₂ Z ∧
      ¬ Z ≤ ballStab 1 μ := by
  obtain ⟨μ, hμ, hμ'⟩ := Nat.sInf_mem (critB_set_nonempty hc)
  exact ⟨μ, hμ, hμ'⟩

end Finite
end Geometry
end CFSG.Quasithin.F112Crit
end
