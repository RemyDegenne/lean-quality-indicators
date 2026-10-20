@[expose] public section

namespace Champernowne

open Filter Asymptotics Topology

theorem champM_pos (b n : ℕ) : 0 < champM b n := Nat.succ_pos _

end Champernowne
end
