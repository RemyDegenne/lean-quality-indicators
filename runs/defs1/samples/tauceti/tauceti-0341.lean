public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

universe u

namespace PreAdicSpace

variable {X Y Z : PreAdicSpace.{u}}

namespace IsOpenImmersion

section Pullback

open Limits

variable (f : X ⟶ Z) [H : IsOpenImmersion f] (g : Y ⟶ Z)

/-- `pullbackConeOfLeft` is a limit cone: a cone over `cospan f g` factors uniquely through the
open immersion `(pullbackConeOfLeft f g).snd`, whose image is `g⁻¹(f(X))`. -/
noncomputable def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  PullbackCone.isLimitAux' _ fun s =>
    have hs : Set.range s.snd.base ⊆ Set.range (pullbackConeOfLeft f g).snd.base := by
      rintro _ ⟨z, rfl⟩
      exact (TopCat.pullback_snd_range f.base g.base).ge
        ⟨s.fst.base z, congrArg (fun φ : s.pt ⟶ Z => φ.base z) s.condition⟩
    ⟨lift _ s.snd hs,
      by rw [← cancel_mono f, Category.assoc, PullbackCone.condition, lift_fac_assoc,
        s.condition],
      lift_fac _ _ _, fun {m} _ hm => lift_uniq _ _ _ m hm⟩

end Pullback
end IsOpenImmersion
end PreAdicSpace
end TauCeti
end
