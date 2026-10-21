namespace OAI

section

section

section

noncomputable section

open Set unitInterval Topology

noncomputable section

noncomputable section

noncomputable section

open Set Topology unitInterval

noncomputable section

open Set Metric Topology unitInterval

noncomputable section

open Set Metric Topology

noncomputable section

noncomputable section

open Set unitInterval

noncomputable section

noncomputable section

open Set Metric Topology

noncomputable section

open Set Metric Topology

noncomputable section

open Set Metric Topology

noncomputable section

open Set Topology

noncomputable section

open Set Topology

noncomputable section

open Set Topology

noncomputable section

open Set Topology unitInterval

namespace CannonWinding

open Set Topology unitInterval Metric

theorem winding_chord_replace (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (q : Path (-1:ℂ) 1) (hq : ∀ t, ‖q t‖=1)
    (sgn : ℝ) (hsgn : sgn=1 ∨ sgn= -1) (hside : ∀ t, sgn*(q t).im≤0)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    ∃ hz : ((sgn*η:ℝ):ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ),
      winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap
        (((sgn*η:ℝ):ℂ)*Complex.I) hz =
      winding (q.trans γ).toContinuousMap 0 (by
        apply path_outside_avoids (q.trans γ) _ (by simp)
        intro t
        rw [Path.trans_apply]
        split_ifs
        · exact (hq _).ge
        · exact hγ _) := by
  let z : ℂ := ((sgn*η:ℝ):ℂ)*Complex.I
  have hnz : ‖z‖<1 := by
    rcases hsgn with rfl|rfl <;> simpa [z,norm_mul,Complex.norm_I,abs_of_pos hη] using hη₁
  have himz : sgn*z.im=η := by
    rcases hsgn with rfl|rfl <;> simp [z]
  have him (s t : I) : sgn*(blendPaths (Path.segment (-1:ℂ) 1) q (s,t)).im≤0 := by
    change sgn*(((1-(s:ℝ)) • Path.segment (-1:ℂ) 1 t+(s:ℝ) • q t).im)≤0
    simp only [Complex.add_im,Complex.smul_im,smul_eq_mul,segment_diameter_im,mul_zero,zero_add]
    nlinarith [hside t,s.property.1]
  let H := (blendPaths (Path.segment (-1:ℂ) 1) q).hcomp (Path.Homotopy.refl γ)
  have hzH : z∉range H := by
    rintro ⟨⟨s,t⟩,he⟩
    change (blendPaths (Path.segment (-1:ℂ) 1) q).hcomp (Path.Homotopy.refl γ) (s,t)=z at he
    rw [Path.Homotopy.hcomp_apply] at he
    split_ifs at he with h
    · change blendPaths (Path.segment (-1:ℂ) 1) q (s,_) = z at he
      have hh := him s ⟨2*(t:ℝ),(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1,h⟩⟩
      rw [he,himz] at hh
      exact hη.not_ge hh
    · exact path_outside_avoids γ hγ hnz ⟨_,he⟩
  have hp : z∉range ((Path.segment (-1:ℂ) 1).trans γ) := by
    rintro ⟨t,ht⟩
    exact hzH ⟨(0,t),by simpa [H] using ht⟩
  refine ⟨hp,?_⟩
  have he := winding_path_homotopy H z hzH
  change winding _ z hp=_
  rw [he]
  apply winding_outside_move (q.trans γ) _ hnz
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact (hq _).ge
  · exact hγ _

end CannonWinding
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
