public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace NormalLayer

section Compositum

variable (L : NormalLayer G) (W : OpenSubgroup G)

variable (F : Formation G)

@[simp]
theorem normQuotientCor_normQuotientRes (hdeg : (L.compositum W).degree = L.degree)
    (x : L.NormQuotient F) :
    L.normQuotientCor W F (L.normQuotientRes W F hdeg x) =
      (L.compositum W).ground.toSubgroup.relIndex L.ground.toSubgroup • x := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [normQuotientRes_mk, normQuotientCor_mk, Formation.levelNorm_inclusion,
      Submodule.Quotient.mk_smul]

end Compositum
end NormalLayer
end TauCeti.ClassFieldTheory
end
