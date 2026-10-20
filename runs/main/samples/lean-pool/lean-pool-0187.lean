@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace DenseOverlay

theorem Snapshot.step_valid (program : Program) (input : List Bool)
    (snapshot : Snapshot) (hvalid : Valid snapshot.overlay) :
    Valid (snapshot.step program input).overlay :=
  Snapshot.step_valid_internal program input snapshot hvalid

end DenseOverlay
end RegisterStore
end RAM
end Complexity
end
