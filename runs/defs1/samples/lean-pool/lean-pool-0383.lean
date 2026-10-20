@[expose] public section

open scoped ContDiff Manifold

open Set TopologicalSpace RS.Cech Module

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {Ω : Opens X}

/-- Multiplication by `f` on `1`-cochains (componentwise `mulOn`). -/
noncomputable def mulC1 (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) (𝒰 : FinCover Ω) :
    C1 D 𝒰 →ₗ[ℂ] C1 E 𝒰 :=
  LinearMap.pi fun p : Fin 𝒰.n × Fin 𝒰.n =>
    (mulOn f hf (𝒰.U p.1 ⊓ 𝒰.U p.2)).comp (LinearMap.proj p)

end RS.Cech
end
