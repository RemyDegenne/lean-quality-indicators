namespace P2MW.S_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

namespace U5FreeSubSol

open CohCarrier IharaLemma

open scoped IsMulCommutative

section Corner

variable (L : ℕ) [NeZero L] (S : Set ℕ) (H : Subgroup (ZMod L)ˣ)
  (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
  {G : Type} (fam : G → Gen L S)
  (hcomm : ∀ g g' : G,
      opFamily L H S 𝒪 (fam g) * opFamily L H S 𝒪 (fam g') = opFamily L H S 𝒪 (fam g') * opFamily L H S 𝒪 (fam g))
  (θbar : G → k)

local notation3 "𝕋" => (CohCarrier.hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra

variable (Sp : IdempotentSplitting ↥(CohCarrier.hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n)

local notation3 "PP" => Pc L S H 𝒪 k fam hcomm θbar Sp i₀

def actP : Sp.CornerRing i₀ →+* Module.End 𝒪 PP where
  toFun z :=
    { toFun := fun m => ⟨((z : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) m,
        Sp.coe_smul_mem i₀ z
          (⟨(m : H1 L H 𝒪), mem_corner L S H 𝒪 k fam hcomm θbar Sp i₀ m⟩ :
            ↥(IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀)))⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun r m => Subtype.ext (LinearMap.map_smul _ r _) }
  map_one' := LinearMap.ext fun m => Subtype.ext (by
    show ((1 : Sp.CornerRing i₀) : ↥𝕋) • (m : H1 L H 𝒪) = m
    rw [IdempotentSplitting.coe_one_cornerRing]
    exact e_smul_of_mem L S H 𝒪 k fam hcomm θbar Sp i₀ (mem_corner L S H 𝒪 k fam hcomm θbar Sp i₀ m))
  map_mul' z w := LinearMap.ext fun m => Subtype.ext (by
    show ((z * w : Sp.CornerRing i₀) : ↥𝕋) • (m : H1 L H 𝒪) =
      (z : ↥𝕋) • ((w : ↥𝕋) • (m : H1 L H 𝒪))
    rw [← mul_smul]
    rfl)
  map_zero' := LinearMap.ext fun m => Subtype.ext (by
    show ((0 : Sp.CornerRing i₀) : ↥𝕋) • (m : H1 L H 𝒪) = 0
    rw [IdempotentSplitting.coe_zero_cornerRing, zero_smul])
  map_add' z w := LinearMap.ext fun m => Subtype.ext (by
    show ((z + w : Sp.CornerRing i₀) : ↥𝕋) • (m : H1 L H 𝒪) =
      (z : ↥𝕋) • (m : H1 L H 𝒪) + (w : ↥𝕋) • (m : H1 L H 𝒪)
    rw [← add_smul]
    rfl)

end Corner
end U5FreeSubSol
end
end P2MW.S_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily
