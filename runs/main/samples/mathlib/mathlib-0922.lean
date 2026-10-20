@[expose] public section

open Function

namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {u v w : V}

@[simp]
theorem reverse_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).reverse = p.reverse.append (cons h.symm nil) := by simp [reverse]

end Walk
end SimpleGraph
end
