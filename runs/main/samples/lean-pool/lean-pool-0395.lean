@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

theorem splitSeed_eq [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (Y : D) (pt : 𝟙_ D ⟶ Y) :
    splitSeed Y pt =
      tensorPowPoint pt 1 ≫ modPowπ (𝟙_ D) Y 1 ≫
        symPowπ (𝟙_ D) Y 1 := by
  rw [splitSeed, tensorPowPoint_one,
    show (symPowOne (𝟙_ D) Y).inv =
      (modPowOne (𝟙_ D) Y).inv ≫ symPowπ (𝟙_ D) Y 1 from rfl,
    modPowOne_inv]
  repeat' erw [Category.assoc]
  rfl

end RS
end
