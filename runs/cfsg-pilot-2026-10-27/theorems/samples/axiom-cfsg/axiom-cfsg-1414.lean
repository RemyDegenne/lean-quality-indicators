public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95IvFact

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

theorem c2_E6 {f : ℕ} (hf : 1 ≤ f) : Char2Order (ordE6 (2 ^ f)) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨f, hf, rfl⟩

end CFSG.LocalAnalysis.GLTheoremB.Prop95IvFact
end
