public section

open scoped commutatorElement

namespace TopologicalAbelianization

section Conjugation

variable {G : Type*} [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]

/-- Conjugation by `G ⧸ N` on `N^{ab}`, as a homomorphism to the automorphism group: the
conjugation action of `G` factored through `G ⧸ N`. It is the homomorphism underlying the
`MulDistribMulAction (G ⧸ N) (TopologicalAbelianization N)` instance below (`conjAut_apply`),
whose defining equation is `mk_smul`. -/
def conjAut : G ⧸ N →* MulAut (TopologicalAbelianization N) :=
  QuotientGroup.lift N
    ((MulDistribMulAction.toMulAut (ConjAct G) (TopologicalAbelianization N)).comp
      ConjAct.toConjAct.toMonoidHom)
    fun _ hg => MonoidHom.mem_ker.2 (MulEquiv.ext (toConjAct_smul_eq_self_of_mem N hg))

end Conjugation
end TopologicalAbelianization
end
