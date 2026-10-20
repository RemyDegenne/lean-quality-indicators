namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_etale_preimage_snd_action_of_etale_nhds

set_option autoImplicit false

universe u

p2m_open

noncomputable section

namespace GoodReductionJacobian

namespace RelativeGroupLaw

namespace SpreadEtale

p2m_open

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {N : Scheme.{u}} {i : N ⟶ G} {S' : Scheme.{u}} {j' : S' ⟶ G}

def fstPt (f : G ⟶ Spec (CommRingCat.of k)) (i : N ⟶ G) (j' : S' ⟶ G) : SchemeHomOver (tP f i j') (i ≫ f) :=
  ⟨pullback.fst (i ≫ f) (j' ≫ f), by rw [pullback.condition]⟩

end SpreadEtale
end RelativeGroupLaw
end GoodReductionJacobian
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_etale_preimage_snd_action_of_etale_nhds
