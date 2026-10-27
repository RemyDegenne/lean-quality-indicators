public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable (τ : Tag)

variable {τ}

section

theorem prodA6_smul {ws : List ℕ} (hws : ∀ g ∈ ws, g < τ.rootCount) (v : Fin τ.rank → ℤ) :
    prodA6 τ ws • v = wordA6 τ ws v := by
  induction ws with
  | nil => simp [prodA6, wordA6]
  | cons g ws ih =>
    have hg : g < τ.rootCount := hws g (by simp)
    have ih' := ih (fun x hx => hws x (by simp [hx]))
    simp only [prodA6, List.map_cons, List.prod_cons] at ih' ⊢
    rw [mul_smul, ih', rootReflection_smul (isRoot_rootVecA6 hg)]
    rfl

end
end CFSG.HardMathSupport.Timmesfeld.CrossChar
end
