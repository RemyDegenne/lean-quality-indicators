@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment Equiv

section InterfaceCut

variable {γ δ : Type}

/-- The identification of the two sides' used labels. -/
def interfaceSideEquiv {V : Fragment (γ ⊕ δ)} (F : EdgeSubset V) (e : γ ≃ δ)
    (hp : InterfacePaired F e) :
    {a : γ // V.boundaryFlag (Sum.inl a) ∈ F.boundaryFlags}
      ≃ {b : δ // V.boundaryFlag (Sum.inr b) ∈ F.boundaryFlags} :=
  e.subtypeEquiv (fun a => hp a)

end InterfaceCut
end EdgeSubset
end RS
end
