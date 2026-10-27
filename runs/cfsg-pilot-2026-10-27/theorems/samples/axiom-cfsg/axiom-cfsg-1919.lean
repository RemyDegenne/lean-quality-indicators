public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier

open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem map_rootGroup_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (t : X) :
    (rootGroup X t).map e.toMonoidHom = rootGroup Y (e t) := by
  have hroots : {y : Y | y * y = e t} = e '' {x : X | x * x = t} := by
    ext y
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq, ← map_mul]
      exact congrArg e hx
  unfold rootGroup
  rw [hroots, MonoidHom.map_closure]
  rfl

end CFSG.EvenSporadicStandard.Fin76b
end
