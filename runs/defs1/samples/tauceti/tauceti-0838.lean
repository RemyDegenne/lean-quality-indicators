open Equiv

public section

namespace TauCeti

namespace TriangleGroup

variable {a b c n : ℕ} (t : PermutationTriple n) (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1)
  (hc : t.σinf ^ c = 1)

section NormalSubgroup

open PermutationTriple

variable (H : Subgroup (TriangleGroup a b c)) (e : TriangleGroup a b c ⧸ H ≃ Fin n)

/-- **Regular triples are finite-index normal subgroups of the triangle group.** For `n ≠ 0`, the
isomorphism classes of regular triples of degree `n` with component orders dividing `a`, `b`, `c`
correspond to the normal subgroups of index `n` of `Δ(a, b, c)`. A class goes to the kernel of the
representation of any of its triples (`TauCeti.TriangleGroup.coe_regularIsoClassEquiv_mk`), and a
normal subgroup `N` to the class of the coset triple of `N`, the action of `Δ(a, b, c)` on
`Δ(a, b, c) ⧸ N` (`TauCeti.TriangleGroup.coe_regularIsoClassEquiv_symm_apply`). -/
noncomputable def regularIsoClassEquiv [NeZero n] :
    regularIsoClasses a b c n ≃
      {N : Subgroup (TriangleGroup a b c) // N.Normal ∧ N.index = n} :=
  (Equiv.ofBijective _ bijective_cosetRegularIsoClass).symm

end NormalSubgroup
end TriangleGroup
end TauCeti
end
