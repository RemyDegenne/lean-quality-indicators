set_option warningAsError true

set_option linter.style.haveILetI false

universe u

namespace MvPolynomial

open Module

public section

theorem exists_anisotropic_homogeneous_of_not_isAlgClosed
    (K : Type u) [Field K] (hK : ¬ IsAlgClosed K) (bound : ℕ) :
    ∃ (d : ℕ) (p : MvPolynomial (Fin d) K),
      bound < d ∧ p.IsHomogeneous d ∧ p.totalDegree = d ∧
        ∀ x : Fin d → K, eval x p = 0 ↔ x = 0 := by
  classical
  have hbad : ¬ ∀ f : Polynomial K, f.Monic → Irreducible f → ∃ x, f.eval x = 0 :=
    fun h => hK (IsAlgClosed.of_exists_root K h)
  push Not at hbad
  obtain ⟨f, _, hf, hnoroot⟩ := hbad
  have hdegree : 1 < f.natDegree := by
    have hpositive : 0 < f.natDegree :=
      Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_irreducible hf)
    have hnotone : f.natDegree ≠ 1 := by
      intro h
      have hdegreeone : f.degree = 1 := by
        simp [Polynomial.degree_eq_natDegree hf.ne_zero, h]
      obtain ⟨x, hx⟩ := Polynomial.exists_root_of_degree_eq_one hdegreeone
      exact hnoroot x hx
    omega
  letI : Fact (Irreducible f) := ⟨hf⟩
  let basis : Basis (Fin f.natDegree) K (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis hf.ne_zero).basis
  let form := NormForms.coordinateNormPolynomial basis
  have homogeneous : form.IsHomogeneous f.natDegree := by
    simpa only [form, Fintype.card_fin] using
      NormForms.coordinateNormPolynomial_isHomogeneous basis
  have anisotropic (x : Fin f.natDegree → K) : eval x form = 0 ↔ x = 0 :=
    NormForms.coordinateNormPolynomial_eval_eq_zero_iff basis x
  letI : Nonempty (Fin f.natDegree) := ⟨⟨0, by omega⟩⟩
  obtain ⟨r, hr⟩ := exists_iteratedBlockSubst_totalDegree_gt form f.natDegree
    homogeneous (fun x hx => (anisotropic x).mp hx) hdegree bound
  let d := f.natDegree ^ r
  have hcard : Fintype.card (Fin r → Fin f.natDegree) = d := by
    simp [d]
  let reindex : (Fin r → Fin f.natDegree) ≃ Fin d :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard)
  let iterate := iteratedBlockSubst form r
  let result := rename reindex iterate
  have htotal : iterate.totalDegree = d :=
    iteratedBlockSubst_totalDegree form f.natDegree homogeneous
      (fun x hx => (anisotropic x).mp hx) r
  refine ⟨d, result, ?_, ?_, ?_, ?_⟩
  · change bound < iterate.totalDegree at hr
    simpa only [htotal] using hr
  · exact (isHomogeneous_iteratedBlockSubst form f.natDegree homogeneous r).rename_isHomogeneous
  · simpa only [result, renameEquiv_apply, htotal] using
      (totalDegree_renameEquiv reindex iterate)
  · intro x
    change eval x (rename reindex iterate) = 0 ↔ x = 0
    rw [eval_rename, show iterate = iteratedBlockSubst form r from rfl,
      eval_iteratedBlockSubst_eq_zero_iff form anisotropic r]
    constructor
    · intro hx
      funext j
      obtain ⟨i, rfl⟩ := reindex.surjective j
      exact congrFun hx i
    · intro hx
      simp [hx]

end
end MvPolynomial
