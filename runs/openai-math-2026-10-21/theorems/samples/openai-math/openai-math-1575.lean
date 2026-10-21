namespace OAI

namespace PowerSaving.Cluster

open Matrix Binary Finset

lemma sync0 (j : J) (F : StartAxes) : syncBox j F (b0 j) eJ := by
  apply sync_J
  intro p h
  simp only [b0,  stamp, ite_eq_left h, basisBox]
  apply ystart_proj (upd_same j F _ _)
  simp [h]

end PowerSaving.Cluster
end OAI
