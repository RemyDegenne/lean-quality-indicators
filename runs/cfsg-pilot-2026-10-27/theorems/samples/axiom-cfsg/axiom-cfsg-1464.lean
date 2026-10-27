public section

namespace CFSG.Quasithin.H13.L32A.E9

open CFSG.Quasithin CFSG.Quasithin.FixR

variable {W : Type} [CommGroup W]

theorem fixed_mul_nu3 (hW : ∀ w : W, w ^ 2 = 1) {x y : MulAut W} (hy : y ^ 3 = 1)
    (hxy : x * y = y * x) {u : W} (hux : nu3Hom x u = 1) (huy : nu3Hom y u = 1) :
    (x * y * y) (u * nu3Hom (x * y) u) = u * nu3Hom (x * y) u := by
  have hsq := mul_self_eq_one hW
  have hinv : ∀ a : W, a⁻¹ = a := fun a => inv_eq_self_of_sq hW a
  have hc : ∀ v, x (y v) = y (x v) := apply_comm hxy
  have key : ∀ (g : MulAut W) (v : W), nu3Hom g v = 1 → g (g v) = v * g v := by
    intro g v h
    rw [nu3Hom_apply] at h
    rw [eq_inv_of_mul_eq_one_right h, hinv]
  have hR1 : x (x u) = u * x u := key x u hux
  have hR2 : y (y u) = u * y u := key y u huy
  have hR3 : x (x (y u)) = y u * x (y u) := by
    refine key x (y u) ?_
    rw [← nu3_comm hxy.symm u, hux, map_one]
  have hxxyy : x (x (y (y u))) = u * x u * (y u * x (y u)) := by
    rw [hR2, map_mul, map_mul, hR1, hR3]
  have hs : u * nu3Hom (x * y) u = u * x u * y u := by
    rw [nu3Hom_apply]
    simp only [MulAut.mul_apply]
    rw [← hc (y u), hxxyy]
    calc u * (u * x (y u) * (u * x u * (y u * x (y u))))
        = (u * u) * (x (y u) * x (y u)) * (u * x u * y u) := by ac_rfl
      _ = u * x u * y u := by rw [hsq, hsq, one_mul, one_mul]
  have e1 : x (y (y u)) = x u * x (y u) := by rw [hR2, map_mul]
  have e2 : x (y (y (x u))) = u * x u * (y u * x (y u)) := by
    rw [← hc u, ← hc (y u), hxxyy]
  have e3 : x (y (y (y u))) = x u := by rw [apply_three hy]
  have hgoal : (x * y * y) (u * x u * y u) =
      x (y (y u)) * x (y (y (x u))) * x (y (y (y u))) := by
    simp only [MulAut.mul_apply, map_mul]
  rw [hs, hgoal, e1, e2, e3]
  calc x u * x (y u) * (u * x u * (y u * x (y u))) * x u
      = (x u * x u) * (x (y u) * x (y u)) * (u * x u * y u) := by ac_rfl
    _ = u * x u * y u := by rw [hsq, hsq, one_mul, one_mul]

end CFSG.Quasithin.H13.L32A.E9
end
