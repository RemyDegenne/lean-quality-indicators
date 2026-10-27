public section

namespace CFSG.QuasithinUnique.Setup.Offender

open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

variable {A : Type*} [Group A]

theorem trivMod_inf_elementary {p : ℕ} [CharP k p] (H : Subgroup (V ≃ₗ[k] V)) :
    CFSG.IsElementaryAbelian p ((H ⊓ trivMod (fixGL H)).subgroupOf H) := by
  have hfix : ∀ x ∈ H, ∀ z ∈ fixGL H, x z = z := fun x hx z hz => hz x hx
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    have ha : (a.1 : V ≃ₗ[k] V) ∈ H ⊓ trivMod (fixGL H) := a.2
    have hb : (b.1 : V ≃ₗ[k] V) ∈ H ⊓ trivMod (fixGL H) := b.2
    exact trivMod_commute (hfix _ ha.1) (hfix _ hb.1) ha.2 hb.2
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
    apply Subtype.ext
    apply Subtype.ext
    have ha : (a.1 : V ≃ₗ[k] V) ∈ H ⊓ trivMod (fixGL H) := a.2
    exact trivMod_pow_char (hfix _ ha.1) ha.2

end CFSG.QuasithinUnique.Setup.Offender
end
