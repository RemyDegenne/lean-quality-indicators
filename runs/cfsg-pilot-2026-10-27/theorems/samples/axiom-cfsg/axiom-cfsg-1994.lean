public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.BenderSuzuki.PFAppendixIII

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem BadLift.starLift
    (hu : BadLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (IH : CanonicalBelow (Nat.card J)) (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) :
    StarLift B z u :=
  ⟨hu.toEscapingLift, hrank, hu.exists_alternating_component h hz IH hrank⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
end
