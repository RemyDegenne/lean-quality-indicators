open Function Set Filter

open scoped Topology BigOperators ComplexConjugate

noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Thermal

open Law Node Real Period

variable {M l : ℕ}

open scoped Classical

lemma moments_bias {p : Node} {P : Law (Grid M)} (hl : l ≤ M)
    {B : Bool} {A : Form M} {s : Finset (Grid l)} {v : Grid l → Grid M → ℂ}
    {β : ℝ} (hG : biases P p A hl s B v β) (Q : Law (Grid l)) (hQ : ∀ x, 0 < Q x → x∈s) :
    let U := P.withNext (channel A)
    β ≤ U.Ex (fun xz => if xz.1∈(p.child B).block M then
        (ply hl Q (fun i => v i xz.2) xz.1).re else 0) := by
  intro U
  let D (i : Grid l) (x : Grid M × Grid M) :=
    if x.1∈(p.child B).block M then (v i x.2*chi (raise hl i) x.1).re else 0
  have H (i : Grid l) (hi : 0 < Q i) : β ≤ U.Ex (D i) := by
    unfold U D; rw [conditional_if_ex P (channel A) (fun x => x∈(p.child B).block M)
      (fun x z => (v i z*chi (raise hl i) x).re)]
    exact hG.2 _ (hQ _ hi)
  calc
    _ = Q.Ex (fun _ => β) := (Q.Ex_const _).symm
    _ ≤ Q.Ex (fun i => U.Ex (D i)) := Q.Ex_mono_mem H
    _ = _ := by
      rw [Ex_swap Q U]
      refine congrArg U.Ex (funext fun x => ?_)
      unfold D
      split_ifs with hh
      · rw [ply,re_Cx]
      rw [Ex_const]

end FourierLLogL.Dyadic.Thermal
end OAI
end
