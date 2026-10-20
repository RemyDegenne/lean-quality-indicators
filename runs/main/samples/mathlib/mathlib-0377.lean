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

variable [IsTopologicalAddGroup W]

theorem add_apply (f g : P →ᴬ[R] W) (x : P) : (f + g) x = f x + g x := rfl

end ModuleValuedMaps
end ContinuousAffineMap
end
