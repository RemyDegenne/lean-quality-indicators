@[expose] public section

open TauCeti.DavisKahan.Angle

open TauCeti.DavisKahan.Sylvester

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

namespace FreeBeam

namespace Model

open DavisKahan1970.Section9

open TauCeti.DavisKahan.TanTheta

open TauCeti.DavisKahan.TanTheta

open TauCeti.DavisKahan.ExactSinTheta

theorem beamPerturbed_finrank_le (ε : ℝ) (hε : 0 ≤ ε)
    {W : Submodule ℂ BeamL2}
    (hW : W ≤ TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic 500) measurableSet_Iic) :
    Module.finrank ℂ W ≤ Module.finrank ℂ beamTrial :=
  TauCeti.LinearPMap.finrank_le_of_le_specRange_Iic (beamPerturbed_isSelfAdjoint ε)
    (β := 1001 / 2) (c := 500) (by norm_num)
    (fun y hy => beamPerturbed_form_ge_of_mem_orthogonal ε hε y hy)
    (fun _ hy => beamPerturbed_specRange_le_domain ε hε hy) hW

end Model
end FreeBeam
end DavisKahan
end TauCeti
end
