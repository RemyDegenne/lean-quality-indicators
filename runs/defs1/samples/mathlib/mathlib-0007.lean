@[expose] public section

noncomputable section Ring

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]

variable {F : Type*} [AddCommGroup F] [Module R F] {G : Type*} [AddCommGroup G] [Module R G]

variable (p q : Submodule R E)

variable {S : Type*} [Semiring S] {M : Type*} [AddCommMonoid M] [Module S M] (m : Submodule S M)

namespace Submodule

open LinearMap

variable {p q}

open Submodule

variable (p q) in
/-- If `q` is a complement of `p`, then `M ⧸ p ≃ q`. The forward direction sends a quotient class
to its projection onto `q` along `p`; the backward direction sends an element of `q` to its class
in `M ⧸ p`. -/
@[simps! symm_apply]
def quotientEquivOfIsCompl (h : IsCompl p q) : (E ⧸ p) ≃ₗ[R] q :=
  .ofLinearMap
    (p.liftQ (q.projectionOnto p h.symm) (by simp))
    (p.mkQ ∘ₗ q.subtype)
    (by ext; simp)
    (by ext; simp [Quotient.eq, sub_mem_comm_iff, sub_projection_mem])

end Submodule
end Ring
end
