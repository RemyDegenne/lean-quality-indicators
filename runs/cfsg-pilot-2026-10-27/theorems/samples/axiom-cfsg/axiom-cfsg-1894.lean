public section

namespace CFSG.Quasithin.H.Code22

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.Mathieu.H16Pf

open scoped commutatorElement

theorem hexHom_eq {σ : HXP} {π : Equiv.Perm (Fin 6)}
    (h : ∀ i, (σ : Equiv.Perm (Fin 24)) (hx i) = hx (π i)) : hexHom σ = π :=
  hex_unique (hexHom_spec σ) h

end CFSG.Quasithin.H.Code22
end
