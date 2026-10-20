@[expose] public section

noncomputable section «lp_nc_section_1»

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

section «lp_section_1»

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section «lp_section_2»

open TermSubst

variable (L)

variable {L}

variable {n m w : V}

lemma _root_.LO.Arith.Language.IsSemitermVec.termSubstVec {k n m v} (hw :
    L.IsSemitermVec n m w) (hv :
    L.IsSemitermVec k n v) :
    L.IsSemitermVec k m (L.termSubstVec k w v) := Language.IsSemitermVec.iff.mpr
  ⟨by simp [hv.isUTerm],
    fun i hi ↦ by rw [nth_termSubstVec hv.isUTerm hi]; exact hw.termSubst (hv.nth hi)⟩

end «lp_section_2»
end «lp_section_1»
end Arith
end LO
end «lp_nc_section_1»
end
