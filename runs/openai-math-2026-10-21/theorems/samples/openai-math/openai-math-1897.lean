namespace OAI

namespace CycleClique

open scoped SimpleGraph

theorem certificate_1843_checked : certificate_1843.Valid 16 8 16 certificate_1843_q certificate_1843_edges 8 3 [] := by decide +kernel

end CycleClique
end OAI
