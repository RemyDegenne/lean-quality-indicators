@[expose] public section

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}

variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

variable {G}

variable (G)

variable {G G' G''}

namespace ConnectedComponent

/-- The `ConnectedComponent` specialization of `Quot.lift`. Provides the stronger
assumption that the vertices are connected by a path. -/
protected def lift {β : Sort*} (f : V → β)
    (h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w) : G.ConnectedComponent → β :=
  Quot.lift f fun v w (h' : G.Reachable v w) => h'.elim_path fun hp => h v w hp hp.2

end ConnectedComponent
end SimpleGraph
end
