@[expose] public section

open CategoryTheory CategoryTheory.Limits TopRep

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {A B C : TopRep.{max v w} k G}

theorem exact_map_connecting [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (n : ℕ) :
    Function.Exact (map (ContinuousMonoidHom.id G) p n).hom
      (connecting i p hi hexact hp n).hom := by
  let S := moduleCochainsSequence i p hexact
  have hS := moduleCochainsSequence_shortExact i p hi hexact hp
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (f₁₂ := (HomologicalComplex.homologyMap S.g n).hom)
    (f₂₃ := (hS.δ n (n + 1) rfl).hom)
    (g₁₂ := (map (ContinuousMonoidHom.id G) p n).hom.toLinearMap)
    (g₂₃ := (connecting i p hi hexact hp n).hom)
    (e₁ := (moduleCohomologyIso B n).toLinearEquiv)
    (e₂ := (moduleCohomologyIso C n).toLinearEquiv)
    (e₃ := (moduleCohomologyIso A (n + 1)).toLinearEquiv)
  · exact congrArg ModuleCat.Hom.hom (moduleCohomologyIso_naturality p n).symm
  · change ModuleCat.Hom.hom ((moduleCohomologyIso C n).hom ≫
      connecting i p hi hexact hp n) =
        ModuleCat.Hom.hom (hS.δ n (n + 1) rfl ≫ (moduleCohomologyIso A (n + 1)).hom)
    exact congrArg ModuleCat.Hom.hom (moduleCohomologyIso_connecting i p hi hexact hp n)
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ n (n + 1) rfl)

end ContinuousCohomology
end
