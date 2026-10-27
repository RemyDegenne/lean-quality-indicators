public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22 Module

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.IdxFour

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour

open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z}

namespace Data41

variable (D : Data41 h)

theorem q0_three : q0 (vecOf 3) = 0 := by rw [q0_vecOf]; decide

end Data41
end CFSG.Quasithin.H13.AS91
end
