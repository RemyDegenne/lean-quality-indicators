@[expose] public section

open scoped ContDiff Manifold

open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The induced cover of a member: `(V ⊓ 𝒱.U α)_α : FinCover V` for `V ≤ ⊤`. -/
def FinCover.induced (𝒱 : FinCover (⊤ : Opens X)) (V : Opens X) : FinCover V where
  n := 𝒱.n
  U := fun α => V ⊓ 𝒱.U α
  le_base := fun _ => inf_le_left
  covers := fun x hx => by
    obtain ⟨α, hα⟩ := 𝒱.covers x trivial
    exact ⟨α, hx, hα⟩

end RS.Cech
end
