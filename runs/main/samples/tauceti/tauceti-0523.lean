public section

namespace TauCeti.TitsLieIndex

noncomputable section

variable (d : TitsLieIndex)

theorem frobenius_def :
    d.frobenius = F4ShortRoot.PrimeField.frobenius 1 d.1.Closure :=
  (rfl)

end
end TauCeti.TitsLieIndex
end
