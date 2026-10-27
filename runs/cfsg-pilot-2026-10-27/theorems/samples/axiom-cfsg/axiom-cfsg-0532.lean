public section

namespace CFSG.Quasithin

open CFSG.Open B19Aux

variable {V : Type*} [CommGroup V]

namespace B19Loc

variable {G A : Subgroup (MulAut V)}

theorem FA_faithful_W [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) {f : MulAut V}
    (hf : f ∈ FAsub G A) (hfix : ∀ w ∈ Wsub G A, f w = w) : f = 1 := by
  refine P.FA_faithful_C hV hf fun c hc => ?_
  obtain ⟨hsup, -⟩ := B1.coprime_decomp hV P.odd_card_FA (M := Csub G A)
    (fun y hy m hm => FA_inv_C hy m hm)
  have hc' : c ∈ (Csub G A ⊓ fixV (FAsub G A)) ⊔ commSub (Csub G A) (FAsub G A) := by
    rw [hsup]; exact hc
  obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.1 hc'
  rw [map_mul, hu.2 f hf, hfix w hw]

end B19Loc
end CFSG.Quasithin
end
