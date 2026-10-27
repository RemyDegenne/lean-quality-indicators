public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

open scoped Pointwise

variable {G : Type*} [Group G]

namespace CosetGeom

variable {G₀ G₁ G₂ T V : Subgroup G}

section Fin

variable [Finite G]

omit [Finite G] in
theorem walk_parity {u v : CosetGeom G₀ G₁ G₂} (p : (graph G₀ G₁ G₂).Walk u v) :
    (vtype u = vtype v ↔ Even p.length) := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have hab := vtype_ne_of_adj h
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← ih]
    revert hab
    cases vtype a <;> cases vtype b <;> cases vtype c <;> simp

end Fin
end CosetGeom
end CFSG.Quasithin
end
