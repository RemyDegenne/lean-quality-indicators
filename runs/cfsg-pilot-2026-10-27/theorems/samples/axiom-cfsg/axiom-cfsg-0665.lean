public section

namespace GL83

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin
  CFSG.Quasithin.F53Push CFSG.LieType.BorelTits

open scoped commutatorElement

namespace I28_3S3

variable {G : Type} [Group G]

theorem sl2_zmod2_fixed_zero : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), A ^ 3 = 1 →
    A ≠ 1 → ∀ v : Fin 2 → ZMod 2, (A : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec v = v → v = 0 := by
  decide +kernel

end I28_3S3
end GL83
end
