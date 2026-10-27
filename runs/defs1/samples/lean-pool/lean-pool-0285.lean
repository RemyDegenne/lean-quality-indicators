@[expose] public section

namespace GoemansFlow

/-- Route every commodity on its zero-cost path. -/
def allZeroCostRoute : Fin 3 → List Arc := zeroCostPath

end GoemansFlow
end
