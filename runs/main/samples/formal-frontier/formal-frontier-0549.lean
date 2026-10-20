set_option autoImplicit false

set_option warningAsError true

public section

open CategoryTheory

noncomputable section

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

namespace CorestrictionTransversal

variable (X : TopRep.{max v w} k G)

attribute [local instance] jointlyContinuous_mackeyStabilizer

variable (X : TopRep.{max v w} k G)

lemma transferCrossed_mackey_apply (H K : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex]
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) (g : K) :
    (transferCrossed X H (mackeyAssembledRightTransversal H K T) f).1 (g : G) =
      (mackeyCrossedSumWithTransversal X H K T f).1 g := by
  classical
  let _ : Fintype (DoubleCoset.Quotient (H : Set G) K) := Fintype.ofFinite _
  let _ (q : DoubleCoset.Quotient (H : Set G) K) :
      Fintype (Subtype (T q : Set K)) := (T q).2.finite_right.fintype
  let S := mackeyAssembledRightTransversal H K T
  let _ : Fintype (Subtype (S : Set G)) := S.2.finite_right.fintype
  let e := mackeyAssembledTransversalEquiv H K T
  change _ =
    (∑ q : DoubleCoset.Quotient (H : Set G) K,
      mackeyTransferCrossedWithTransversal X H K q.out (T q)
        (mackeyConjugateCrossed X H K q.out f)).1 g
  rw [show
    (∑ q : DoubleCoset.Quotient (H : Set G) K,
      mackeyTransferCrossedWithTransversal X H K q.out (T q)
        (mackeyConjugateCrossed X H K q.out f)).1 g =
      ∑ q : DoubleCoset.Quotient (H : Set G) K,
        (mackeyTransferCrossedWithTransversal X H K q.out (T q)
          (mackeyConjugateCrossed X H K q.out f)).1 g from by
    let F := fun q : DoubleCoset.Quotient (H : Set G) K =>
      mackeyTransferCrossedWithTransversal X H K q.out (T q)
        (mackeyConjugateCrossed X H K q.out f)
    have hcoe :
        ((↑(∑ q, F q) : C(K, X))) = ∑ q, (F q).1 := by
      simpa only using
        (Submodule.coe_sum (p := continuousCrossedHom (TopRep.res K.subtype X))
          F Finset.univ)
    calc
      (∑ q, F q).1 g = (∑ q, (F q).1) g :=
        congrArg (fun c : C(K, X) => c g) hcoe
      _ = ∑ q, (F q).1 g := by
        change ContinuousMap.evalCLM k g (∑ q, (F q).1) = _
        rw [map_sum]
        rfl]
  rw [transferCrossed_apply]
  calc
    (∑ s : Subtype (S : Set G),
        X.ρ (s.1⁻¹) (f.1 (factor S s (g : G)))) =
      ∑ p : Sigma fun q => Subtype (T q : Set K),
        X.ρ ((e p).1⁻¹) (f.1 (factor S (e p) (g : G))) := by
          exact (e.sum_comp fun s : Subtype (S : Set G) =>
            X.ρ (s.1⁻¹) (f.1 (factor S s (g : G)))).symm
    _ = ∑ q : DoubleCoset.Quotient (H : Set G) K,
        ∑ t : Subtype (T q : Set K),
          X.ρ ((q.out * (t.1 : G))⁻¹)
            (f.1 (⟨q.out *
              (((factor (G := K) (T q) t g :
                mackeyOpenStabilizer H K q.out) : K) : G) * q.out⁻¹,
              (factor (G := K) (T q) t g).2⟩ : H)) := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro q _
          apply Finset.sum_congr rfl
          intro t _
          change X.ρ
              ((mackeyAssembledRepresentativeMem H K T q t).1⁻¹)
              (f.1 (factor S
                (mackeyAssembledRepresentativeMem H K T q t) (g : G))) = _
          rw [mackeyAssembledRepresentativeMem_coe,
            mackeyAssembled_factor]
    _ = ∑ q : DoubleCoset.Quotient (H : Set G) K,
        (mackeyTransferCrossedWithTransversal X H K q.out (T q)
          (mackeyConjugateCrossed X H K q.out f)).1 g := by
          apply Finset.sum_congr rfl
          intro q _
          let _ := mackeyOpenStabilizerFiniteIndex H K q.out
          rw [show mackeyTransferCrossedWithTransversal X H K q.out (T q) =
              transferCrossed (TopRep.res K.subtype X)
                (mackeyOpenStabilizer H K q.out) (T q) from rfl]
          rw [transferCrossed_apply]
          apply Finset.sum_congr rfl
          intro t _
          rw [mackeyConjugateCrossed_apply]
          change X.ρ ((q.out * (t.1 : G))⁻¹) _ =
            X.ρ (t.1 : G)⁻¹ (X.ρ q.out⁻¹ _)
          rw [mul_inv_rev, rho_mul_apply]
          apply congrArg (X.ρ ((t.1 : G)⁻¹ * q.out⁻¹))
          apply congrArg f.1
          apply Subtype.ext
          rfl

end CorestrictionTransversal
end ContinuousCohomology
end
end
