public noncomputable section

open CategoryTheory Representation

namespace TauCeti.ClassFieldTheory

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

namespace NormalLayer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (L : NormalLayer G)

section Norm

variable (F : Formation G)

section GroundEquiv

variable {A : Type*} [Group A] {N : Subgroup A} (e : Additive A ≃+ F.level L.ground)

@[simp]
theorem normQuotientEquivOfGroundEquiv_mk [N.Normal]
    (hN : ∀ a, e (.ofMul a) ∈ L.normSubgroup F ↔ a ∈ N) (a : A) :
    L.normQuotientEquivOfGroundEquiv F e hN (.ofMul (a : A ⧸ N)) =
      L.normQuotientMk F (e (.ofMul a)) := by
  rw [normQuotientEquivOfGroundEquiv, QuotientGroup.quotientKerEquivOfSurjective,
    AddEquiv.toMultiplicativeRight_symm_apply_apply, toMul_ofMul, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.quotientKerEquivOfRightInverse_apply,
    QuotientGroup.kerLift_mk, groundNormQuotientHom_apply, toAdd_ofAdd]

end GroundEquiv
end Norm
end NormalLayer
end TauCeti.ClassFieldTheory
end
