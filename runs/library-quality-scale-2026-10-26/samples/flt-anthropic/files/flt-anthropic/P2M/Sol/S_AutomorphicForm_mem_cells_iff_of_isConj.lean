import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import P2M.Util
namespace P2MW.S_AutomorphicForm_mem_cells_iff_of_isConj

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsCentralType IsUnipotentType IsHyperbolicType IsEllipticType centralCell unipotentCell hyperbolicCell ellipticCell mem_unipotentCell_iff mem_hyperbolicCell_iff mem_ellipticCell_iff"
p2m_open "AutomorphicForm"

theorem _root_.P2MW.S_AutomorphicForm_mem_cells_iff_of_isConj.solution (K : Type) [Field K] (γ δ : GL (Fin 2) K) (h : IsConj γ δ) :
    (γ ∈ centralCell K ↔ δ ∈ centralCell K) ∧ (γ ∈ unipotentCell K ↔ δ ∈ unipotentCell K) ∧
      (γ ∈ hyperbolicCell K ↔ δ ∈ hyperbolicCell K) ∧ (γ ∈ ellipticCell K ↔ δ ∈ ellipticCell K) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h

  have hδ : ((δ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (c : Matrix (Fin 2) (Fin 2) K) * (γ : Matrix (Fin 2) (Fin 2) K) * ((c⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [← hc]; rfl
  have hcp : ((δ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly
      = ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [hδ, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj c _

  have hcen : ∀ (γ' δ' : GL (Fin 2) K), IsConj γ' δ' →
      IsCentralType ((γ' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) →
        IsCentralType ((δ' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro γ' δ' h' ⟨a, ha⟩
    obtain ⟨c', hc'⟩ := isConj_iff.mp h'
    refine ⟨a, ?_⟩
    rw [← hc']
    show (c' : Matrix (Fin 2) (Fin 2) K) * (γ' : Matrix (Fin 2) (Fin 2) K) * ((c'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
    rw [ha, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Matrix.GeneralLinearGroup.coe_mul,
      mul_inv_cancel]
    rfl
  have hcen_iff : IsCentralType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ↔
      IsCentralType ((δ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    ⟨hcen γ δ h, hcen δ γ h.symm⟩
  refine ⟨hcen_iff, ?_, ?_, ?_⟩
  · simp only [mem_unipotentCell_iff, IsUnipotentType, hcp, hcen_iff]
  · simp only [mem_hyperbolicCell_iff, IsHyperbolicType, hcp]
  · simp only [mem_ellipticCell_iff, IsEllipticType, hcp]

end AutomorphicForm
