@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

variable {G}

/-- The dart with reversed orientation from a given dart. -/
@[simps]
def Dart.symm (d : G.Dart) : G.Dart :=
  ⟨d.toProd.swap, d.adj.symm⟩

end SimpleGraph
end
