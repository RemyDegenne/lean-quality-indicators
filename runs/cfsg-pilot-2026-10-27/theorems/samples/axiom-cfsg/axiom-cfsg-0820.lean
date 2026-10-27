public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem Dbl.im_baum_eq {t : G} (D : Dbl T M H S L t) (P : A5Pi L) :
    P.im (baum S) = P.im (thompsonJ S) := by
  obtain ⟨τ₁, τ₂, -, -, -, hJeq, hBeq, -⟩ := D.core_B P
  exact hBeq.trans hJeq.symm

end CFSG.QuasithinUnique.AppCS2
end
