public section

namespace TauCeti

variable {n a b c : ℕ}

@[simp] theorem mem_connectedTriplesWithExactOrders {t : PermutationTriple n} :
    t ∈ connectedTriplesWithExactOrders n a b c ↔ t.IsConnected ∧ t.HasExactOrders a b c := by
  simp [connectedTriplesWithExactOrders]

end TauCeti
end
