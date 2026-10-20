public section

namespace TauCeti

open CategoryTheory ContCohomology _root_.TauCeti.ContinuousCohomology

universe u

attribute [local instance 2000] Ring.toAddCommGroup

attribute [local instance] trivialZModAction

local instance integralAction (G : Type u) [Monoid G] : DistribMulAction G ℤ :=
  trivialZModAction 0 G

local instance : IsAddTorsionFree (ULift.{u} ℤ) :=
  Function.Injective.isAddTorsionFree
    (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).toAddMonoidHom ULift.down_injective

variable (G : Type u) [Group G]

variable [TopologicalSpace G] [IsTopologicalGroup G]

local instance integralContinuousSMul : ContinuousSMul G (ULift.{u} ℤ) := ⟨continuous_snd⟩

local instance cyclicContinuousSMul (n : ℕ) : ContinuousSMul G (ULift.{u} (ZMod n)) :=
  ⟨continuous_snd⟩

variable [CompactSpace G]

@[simp]
theorem integralBockstein_modulus_one (i : ℕ) : integralBockstein G 1 i = 0 := by
  apply ConcreteCategory.hom_ext
  intro x
  have h := (mem_range_integralBockstein_iff G 1 i _).1 ⟨x, rfl⟩
  simpa using h

end TauCeti
end
