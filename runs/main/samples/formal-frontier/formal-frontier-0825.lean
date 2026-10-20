@[expose] public section

noncomputable section

universe u

namespace Subgroup.RightTransversal

variable {G : Type u} [Group G]

section Representatives

variable {H : Subgroup G} (T : H.RightTransversal)

lemma changeFactor_mul_changeRep (S : H.RightTransversal) (t : ↥(T : Set G)) :
    (changeFactor T S t : G) * (changeRep T S t : G) = (t : G) :=
  S.2.equiv_fst_mul_equiv_snd _

end Representatives
end Subgroup.RightTransversal
end
end
