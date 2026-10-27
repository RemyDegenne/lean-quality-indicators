public noncomputable section

open unitInterval ContinuousMap

namespace Path

variable {X : Type*} [TopologicalSpace X] {w x y z : X}

/-- The straight-line homotopy from the identity of the path space to reparametrization by `f`,
evaluating `Path.Homotopy.reparam γ f` at each time. It is continuous in the path. -/
def reparamHomotopy (f : I → I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    ContinuousMap.Homotopy (ContinuousMap.id (Path x y))
      ⟨fun γ ↦ γ.reparam f hf hf₀ hf₁, by fun_prop⟩ where
  toFun q := (Homotopy.reparam q.2 f hf hf₀ hf₁).eval q.1
  continuous_toFun := continuous_uncurry_iff.mp <|
    (continuous_snd.comp continuous_fst).eval <| by fun_prop
  map_zero_left γ := by simp
  map_one_left γ := by simp

end Path
end
