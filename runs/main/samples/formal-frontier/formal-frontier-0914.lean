@[expose] public section

set_option warningAsError true

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

namespace PartialMap

theorem pullsDenseOpens_restrict_iff (f : X.PartialMap Y) (W : X.Opens)
    (hW : Dense (W : Set X)) (hWf : W ≤ f.domain) :
    (f.restrict W hW hWf).PullsDenseOpens ↔ f.PullsDenseOpens :=
  pullsDenseOpens_iff_of_equiv _ _ (f.restrict_equiv W hW hWf)

end PartialMap
end AlgebraicGeometry.Scheme
end
