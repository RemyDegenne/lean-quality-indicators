public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open Equiv

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_centralizer_conj {V : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (s : G) :
    (V ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set G)).relIndex V =
      (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V := by
  set f : G →* G := (MulAut.conj g).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj g).injective
  have hfx : ∀ x, f x = g * x * g⁻¹ := fun x => rfl
  have hginv : g⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hg
  have hV : V.map f = V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hfx]
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hginv x).mp hx
        simpa using this
      · rw [hfx]; group
  have hC : (V ⊓ Subgroup.centralizer ({s} : Set G)).map f =
      V ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyV, hys⟩ := Subgroup.mem_inf.mp hy
      rw [hfx]
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hyV, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Commute.conj (Subgroup.mem_centralizer_singleton_iff.mp hys) g)
    · intro hx
      obtain ⟨hxV, hxs⟩ := Subgroup.mem_inf.mp hx
      refine ⟨g⁻¹ * x * g, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hginv x).mp hxV
        simpa using this
      · have hc : Commute x (g * s * g⁻¹) := Subgroup.mem_centralizer_singleton_iff.mp hxs
        have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        rw [e] at hc
        exact Subgroup.mem_centralizer_singleton_iff.mpr ((Commute.conj_iff g).mp hc)
      · rw [hfx]; group
  calc (V ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set G)).relIndex V
      = ((V ⊓ Subgroup.centralizer ({s} : Set G)).map f).relIndex (V.map f) := by rw [hC, hV]
    _ = (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V :=
      Subgroup.relIndex_map_map_of_injective _ _ hfinj

end F53.Stellmacher
end CFSG.Quasithin
end
