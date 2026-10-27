public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem positive_root_collection
    (τ : Tag) (R : Type) [CommRing R] :
    (∀ S : Set (Fin τ.rank → ℤ), (∀ α ∈ S, IsRoot τ α ∧ 0 < height α) →
      (∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
        a • α + b • β ∈ S) →
      ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
        Set.BijOn (fun c : Fin m → R => (List.ofFn fun i => pinnedX τ R (α i) (c i)).prod)
          Set.univ (rootSpan τ R S)) ∧
    ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α →
      Set.range α = {β | IsRoot τ β ∧ 0 < height β} →
      Set.BijOn (fun c : Fin m → R => (List.ofFn fun i => pinnedX τ R (α i) (c i)).prod)
        Set.univ (posUnipotent τ R) := by
  refine ⟨fun S hS hclosed m α hα hrange => bijOn_prod_pinnedX R hS hclosed α hα hrange,
    fun α hα hrange => bijOn_prod_pinnedX R (fun β hβ => hβ) (fun β hβ γ hγ a b ha hb hr => ?_)
      α hα hrange⟩
  refine ⟨hr, ?_⟩
  rw [height_nsmul_add_nsmul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith [hβ.2, hγ.2]

end CFSG.LieType.Chevalley
end
