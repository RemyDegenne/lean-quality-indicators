public section

namespace TauCeti.DiscreteCoind

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
  [U.FiniteIndex] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-- **The kernel of the trace** `Coind_U^G M → M`, as an additive subgroup of the coinduced
module. It is `G`-stable (`TauCeti.DiscreteCoind.smul_mem_traceKer`), and carries the restricted
action of `G` as an instance. -/
noncomputable def traceKer : AddSubgroup (DiscreteCoind G U M) := (trace G U M).toAddMonoidHom.ker

end TauCeti.DiscreteCoind
end
