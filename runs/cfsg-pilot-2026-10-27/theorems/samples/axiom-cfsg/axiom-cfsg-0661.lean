public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Fam15

variable {M V₀ V U S H' : Subgroup G}

theorem weakly_closed (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) (hF : Fam15 V₀ V U S H') {g : G} (hg : g ∈ H')
    (hle : conjSubgroup V₀ g ≤ M) : g ∈ M := by
  by_contra hgM
  apply hgM
  have hcomm := hF.conj_comm hI hS h hg hle hgM
  have hUW : U ≤ zSub15 V₀ U H' ⊓ V := le_inf (le_sup_left.trans (le_conjClosure _ _)) h.le
  refine h.mem_M_of_conj_le hI hS (le_inf hle fun y hy => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (hcomm y hy u (hUW hu)).symm

end Fam15
end CFSG.LocalAnalysis.WeakClosure81
end
