namespace OAI

namespace TuringRigidity.RegularCodeSplitting

open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra

open InternalRegularOrder InternalBooleanDense

theorem partition_join (c U V W : ZFSet.{0}) (hU : IsCode c U)
    (hV : IsCode c V) (hW : IsCode c W) (h : Partition U V W) :
    supCode c {V,W} = U := by
  have hF : ∀ X ∈ ({V,W} : ZFSet.{0}), IsCode c X := fun X hX =>
    (ZFSet.mem_pair.mp hX).elim (fun he => he ▸ hV) (fun he => he ▸ hW)
  have hle := (supCode_le_iff c {V,W} U hF hU).mpr (fun X hX =>
    (ZFSet.mem_pair.mp hX).elim (fun he => he ▸ h.1) (fun he => he ▸ h.2.1))
  apply ZFSet.ext; intro p
  refine ⟨fun hp => hle hp,fun hp => ?_⟩
  apply (mem_regular c _ p).mpr
  refine ⟨hU.1 hp,fun q hq hpq => ?_⟩
  obtain ⟨r,_,hqr,hr⟩ := h.2.2.2.2.2 q (code_lower c U hU p hp q hq hpq)
  refine ⟨r,?_,hqr⟩
  exact hr.elim (fun hr => ZFSet.mem_sUnion.mpr ⟨V,ZFSet.mem_pair.mpr (Or.inl rfl),hr⟩)
    (fun hr => ZFSet.mem_sUnion.mpr ⟨W,ZFSet.mem_pair.mpr (Or.inr rfl),hr⟩)

end TuringRigidity.RegularCodeSplitting
end OAI
