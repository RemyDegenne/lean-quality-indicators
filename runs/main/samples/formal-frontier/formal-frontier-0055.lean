@[expose] public section

universe uR uM

namespace LinearMap

@[simp] theorem commutingIdempotentsEquiv_apply_snd_fst
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) (x : M) :
    ((commutingIdempotentsEquiv p q hp hq hpq x).2.1 : M) = ((1 - p) * q) x := by
  simp only [commutingIdempotentsEquiv, LinearEquiv.trans_apply]
  simpa using congrArg (fun e : Module.End R M ↦ e x)
    (jointProjector_pair p q hpq ![false, true])

end LinearMap
end
