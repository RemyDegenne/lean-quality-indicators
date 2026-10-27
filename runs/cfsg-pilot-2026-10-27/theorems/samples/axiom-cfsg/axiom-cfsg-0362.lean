public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

open scoped commutatorElement MatrixGroups

variable {Y : Type} [Group Y] [Finite Y] {s : Y} {K : Subgroup Y}

variable {Y : Type} [Group Y] [Finite Y] {s : Y} {K : Subgroup Y}

omit [Finite Y] in
theorem KPair.central_extension {K' : Subgroup Y}
    (hcen : ∀ n ∈ pPrimeCore 2 Y, ∀ k ∈ K ⊔ K', n * k = k * n)
    {L : Subgroup (barQ Y)} (hgen : K.map (barMk Y) ⊔ K'.map (barMk Y) = L) :
    ∃ φ : ↥(K ⊔ K') →* ↥L, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center ↥(K ⊔ K') := by
  have hmap : (K ⊔ K').map (barMk Y) = L := by rw [Subgroup.map_sup, hgen]
  let φ : ↥(K ⊔ K') →* ↥L :=
    ((barMk Y).comp (K ⊔ K').subtype).codRestrict L (fun g => by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ g.2)
  refine ⟨φ, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    rw [← hmap] at hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨g, hg⟩, rfl⟩
  · intro g hg
    have h1 : barMk Y (g : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
    have h2 : (g : Y) ∈ pPrimeCore 2 Y := by
      rw [← ker_barMk]; exact MonoidHom.mem_ker.mpr h1
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact (hcen _ h2 k k.2).symm

end CFSG.GH74.GLS.LU.Local
end
