set_option autoImplicit false

namespace CerednikDrinfeld

namespace FormalOmega

namespace AlgFunctor

variable {𝒪 : Type} [CommRing 𝒪]

structure GroupAction (Γ : Type) [Group Γ] (F : AlgFunctor 𝒪) : Type 1 where

  act : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Γ → F.obj B → F.obj B
  act_one : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : F.obj B), act B 1 x = x
  act_mul : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g h : Γ) (x : F.obj B), act B (g * h) x = act B g (act B h x)

  act_map : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (g : Γ) (x : F.obj B), F.map f (act B g x) = act B' g (F.map f x)

end AlgFunctor
end FormalOmega
end CerednikDrinfeld
