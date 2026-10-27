public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

namespace L619

open CFSG.LieType.BorelTits CFSG.Quasithin

theorem nonempty_gl2_mulEquiv_perm3' :
    Nonempty (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 3)) := by
  let ua : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩
  let ub : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    ⟨!![1, 0; 1, 1], !![1, 0; 1, 1], by decide, by decide⟩
  have hab : ua * ub ≠ ub * ua := fun h => absurd (congrArg Units.val h) (by decide)
  exact CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six card_GL_two_two ua ub hab

end L619
end CFSG.Quasithin.H13
end
