@[expose] public section

@[inherit_doc] notation:25 E " →ₛₗ.[" σ:25 "] " F:0 => LinearPMap σ E F

notation:25 E " →ₗ.[" R:25 "] " F:0 => LinearPMap (RingHom.id R) E F

variable {R S T : Type*} [Ring R] [Ring S] [Ring T] {σ : R →+* S} {τ : S →+* T} {E : Type*}
  [AddCommGroup E] [Module R E] {F : Type*} [AddCommGroup F] [Module S F] {G : Type*}
  [AddCommGroup G] [Module T G]

namespace LinearPMap

/-- `f.coprod g` is the partially defined linear map defined on `f.domain × g.domain`,
and sending `p` to `f p.1 + g p.2`. -/
def coprod [Module R F] [Module S G] (f : E →ₛₗ.[σ] G) (g : F →ₛₗ.[σ] G) : E × F →ₛₗ.[σ] G where
  domain := f.domain.prod g.domain
  toFun :=
    (show f.domain.prod g.domain →ₛₗ[σ] G from
      (f.comp (LinearPMap.fst f.domain g.domain) fun x => x.2.1).toFun) +
    (show f.domain.prod g.domain →ₛₗ[σ] G from
      (g.comp (LinearPMap.snd f.domain g.domain) fun x => x.2.2).toFun)

end LinearPMap
end
