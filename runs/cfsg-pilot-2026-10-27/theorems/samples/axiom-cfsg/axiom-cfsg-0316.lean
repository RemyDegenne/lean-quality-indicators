public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

open CFSG.QuasithinUnique.AppC

variable {G : Type} [Group G] [Finite G]

namespace GMate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : GCfg T M H S L) (m : GMate S T M₀ x)

include C m

variable (F : GFour C x)

theorem type_conj_Y {s : G} (hsS : s ∈ S) (hsB : s ∉ baum S) :
    ∀ g, g ∈ C.P.im (conjR F.Y s) ↔ g = 1 ∨ g = swap 2 3 := by
  intro g
  have hYS : F.Y ≤ S := (m.Yv_isMax C F.hv F.hπ).1.1
  have hY : ∀ g, g ∈ C.P.im F.Y ↔ g = 1 ∨ g = swap 0 1 := m.Yv_type C F.hv F.hπ
  have h := C.mem_im_conj_inv (inv_mem hsS) hYS (g := g)
  rw [inv_inv, C.P.pf_inv (hsS), inv_inv] at h
  show g ∈ C.P.im (conjSubgroup F.Y s) ↔ _
  rw [h, hY]
  have hD : C.P.pf s ∈ Dset := by
    have : C.P.pf s ∈ C.P.im S := (C.P.mem_im_pf le_rfl).2 ⟨s, hsS, rfl⟩
    rw [C.hS] at this
    exact (mem_Dstd _).1 this
  have hnE : C.P.pf s ∉ Eset := fun h => hsB (m.mem_B_of_pf C hsS h)
  exact conj_D_cases _ hD hnE g

end GMate
end CFSG.QuasithinUnique.AppD
end
