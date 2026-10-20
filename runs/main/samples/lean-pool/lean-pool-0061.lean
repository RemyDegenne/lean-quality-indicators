@[expose] public section

namespace BeyondBethe

open Complexity

theorem machineCertificateSourceWord_mem_FP :
    machineCertificateSourceWord ∈ Complexity.FP :=
  machinePairFirst_mem_FP

end BeyondBethe
end
