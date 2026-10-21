namespace OAI

namespace PartitionConsistency.SetForcingNames.SymmetricSystem

universe u v w

noncomputable section

variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]

variable (S : SymmetricSystem.{u} P Γ)

theorem cartesianName_fixed (X Y : S.Name) (g : Γ) (hx : g • X = X) (hy : g • Y = Y) :
    g • S.cartesianName X Y = S.cartesianName X Y :=
  Subtype.ext (S.collectName_fixed _ _ (S.productSupport X Y) (S.product_permute X Y)
    g ⟨congrArg Subtype.val hx,congrArg Subtype.val hy⟩)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem
end OAI
