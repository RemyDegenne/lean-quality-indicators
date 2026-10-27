namespace P2MW.S_ModularCurve_PDPairing_index_Gamma_four

set_option autoImplicit false

open scoped MatrixGroups

p2m_reactivate

section InlinedSchreier

namespace ModularCurve

namespace PDPairing

namespace Schreier

p2m_open

variable {G : Type*} [Group G] {V : Type*} [MulAction G V] {ι : Type*}

p2m_reactivate

p2m_reactivate

namespace TreeTransversal

variable {a : ι → G} {v₀ : V} (T : TreeTransversal a v₀)

noncomputable def wordWalk (v : V) : List (ι × Bool) → MulAction.stabilizer G v₀
  | [] => 1
  | p :: l => T.sx (wprod a l • v) p * wordWalk v l

end TreeTransversal
end Schreier
end PDPairing
end ModularCurve
end InlinedSchreier
end P2MW.S_ModularCurve_PDPairing_index_Gamma_four
