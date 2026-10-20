@[expose] public section

namespace Quiver

universe v v₁ v₂ u u₁ u₂

variable {V : Type*} [Quiver V] {W : Type*} (σ : V → W)

/-- The `Quiver` instance obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint unusedArguments]
def Push (_ : V → W) :=
  W

end Quiver
end
