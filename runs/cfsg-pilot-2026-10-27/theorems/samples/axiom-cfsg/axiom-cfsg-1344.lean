public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

open scoped Pointwise

section InnerW

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d36Inner_holds : D36Inner := by
  intro hL38 W _ _ M Mp T L V t n g hg m hm hgU hgsq hmsq hinn u hu
  have hd : InnerData T L (orbSup T V) g m :=
    ⟨hg, d36nd_normalizer hL38 n hg hgU, hm, hgsq, hmsq, hinn⟩
  let F : Subgroup W :=
    { carrier := {x | (m⁻¹ * g) x = x}
      one_mem' := map_one _
      mul_mem' := fun {a b} ha hb => by
        have ha' : (m⁻¹ * g) a = a := ha
        have hb' : (m⁻¹ * g) b = b := hb
        show (m⁻¹ * g) (a * b) = a * b
        rw [map_mul, ha', hb']
      inv_mem' := fun {a} ha => by
        have ha' : (m⁻¹ * g) a = a := ha
        show (m⁻¹ * g) a⁻¹ = a⁻¹
        rw [map_inv, ha'] }
  have hF : commSub (orbSup T V) L ≤ F := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, hw, rfl⟩
    exact hd.fixes_comm hL38 n hw hl
  have h1 : (m⁻¹ * g) u = u := hF hu
  have h2 : m⁻¹ (g u) = u := h1
  have h3 := congrArg m h2
  rw [MulAut.apply_inv_self (M := W)] at h3
  exact h3

end InnerW
end CFSG.Quasithin
end
