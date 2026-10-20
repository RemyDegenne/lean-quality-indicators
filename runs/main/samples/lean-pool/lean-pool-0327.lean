public section

namespace NFChoice.Foundation.ExactLiteralTrial

open scoped Fol

open LiteralClass

theorem axCnv_source_equation :
    literalAxCnv =
      .all
        (Formula.ex
          (.all (.all (Formula.biimp (literalPairMem 1 0 2) (literalPairMem 0 1 3))))) :=
  rfl

end NFChoice.Foundation.ExactLiteralTrial
end
