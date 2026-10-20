public section

namespace TauCeti

namespace DynkinType

@[simp] lemma rootLength_F4 :
    F4.rootLength = fun i : Fin F4.rank ↦ if (i : ℕ) < 2 then (2 : ℤ) else 1 := (rfl)

end DynkinType
end TauCeti
end
