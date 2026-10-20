@[expose] public section

universe u

open CategoryTheory Opposite

theorem uliftZMultiplesHom_apply_add (G : Type u) [AddCommGroup G] (x y : G) :
    uliftZMultiplesHom G (x + y) = uliftZMultiplesHom G x + uliftZMultiplesHom G y := by
  ext
  simp_all only [uliftZMultiplesHom_apply_apply, smul_add, AddMonoidHom.add_apply]

end
