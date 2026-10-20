@[expose] public section

notation:25 P " →ᴬ[" R "] " Q => ContinuousAffineMap R P Q

namespace ContinuousAffineMap

variable {R V W P Q : Type*} [Ring R]

variable [AddCommGroup V] [Module R V] [TopologicalSpace P] [AddTorsor V P]

variable [AddCommGroup W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

variable (R P)

variable {R P} {W₂ Q₂ : Type*}

variable [AddCommGroup W₂] [Module R W₂] [TopologicalSpace Q₂] [AddTorsor W₂ Q₂]

section ModuleValuedMaps

variable {S : Type*}

variable [TopologicalSpace W]

section MulAction

variable [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]

variable [ContinuousConstSMul S W]

theorem smul_apply (t : S) (f : P →ᴬ[R] W) (x : P) : (t • f) x = t • f x := rfl

end MulAction
end ModuleValuedMaps
end ContinuousAffineMap
end
