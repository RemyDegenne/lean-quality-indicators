public section

open Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A space is **semilocally simply connected at `x`** if `x` has a neighbourhood `U` such that
every loop in `U` based at `x` is null-homotopic in the whole space. The null-homotopy is allowed
to leave `U`, which is what makes this weaker than local simple connectivity. This is the based
notion of Brazas, Definition 2.1 (see the References below). -/
def _root_.SemilocallySimplyConnectedAt (x : X) : Prop :=
  ∃ U ∈ 𝓝 x, ∀ γ : Path x x, Set.range γ ⊆ U → γ.Homotopic (Path.refl x)

end TauCeti
end
