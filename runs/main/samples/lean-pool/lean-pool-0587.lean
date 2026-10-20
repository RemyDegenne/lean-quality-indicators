@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem nodup_of_mem_edgeOrders (F : Forest V)
    {order : List (Edge V)} (h : order ∈ F.edgeOrders) :
    order.Nodup :=
  ((F.mem_edgeOrders_iff_toFinset_eq_and_nodup).mp h).2

end Forest
end BKAR
end
end
