public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed

variable {G : Type} [Group G]

theorem q8Fam_conj : ConjInvariant (q8Fam G) := by
  intro n K hK
  obtain ⟨e⟩ := hK
  exact ⟨(K.equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective).symm.trans e⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23
end
