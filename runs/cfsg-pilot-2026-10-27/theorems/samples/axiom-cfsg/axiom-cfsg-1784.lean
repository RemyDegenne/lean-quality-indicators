public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Certificates

open scoped Pointwise

set_option linter.unusedSectionVars false

section Normalizer

theorem lab_lt (p : Fin 819) : ovUForest.1[(p : ℕ)]! < 6 :=
  (orbitLabelOK_parts ovU_parts.2.2.2.2.1).1 p p.2

end Normalizer
end CFSG.Quasithin.D4Hex
end
