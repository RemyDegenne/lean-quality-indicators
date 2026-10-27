public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

namespace O2Mod

variable {H : Type} [Group H] {E μ : Set H}

namespace IsTwinSection

variable (hμ : IsTwinSection E μ) (hP : Pair H E)

include hμ hP

theorem mate_mate_mate_ne_of_affine {f g k : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hk : k ∈ E) (hfg : f * g ≠ g * f) (hgk : g * k ≠ k * g) (hfk : f * k ≠ k * f)
    (hc : k * (f * g * f) ≠ f * g * f * k) :
    mate E μ (mate E μ (mate E μ f g) k) f ≠ f := by
  intro heq
  set f' := mate E μ f g with hf'
  have hf'E := hμ.mate_mem hP hf hfμ hg hfg
  have hf'μ := hμ.mate_notMem hP hf hfμ hg hfg
  have hgf' := hμ.isTwin_mate hP hf hfμ hg hfg
  have hff' := hμ.mate_not_commute hP hf hfμ hg hfg
  have hf'k : f' * k ≠ k * f' := not_commute_of_isTwin hgf' hk hgk
  set f'' := mate E μ f' k with hf''
  have hf''E := hμ.mate_mem hP hf'E hf'μ hk hf'k
  have hkf'' := hμ.isTwin_mate hP hf'E hf'μ hk hf'k
  have hf''f : f'' * f ≠ f * f'' := fun e => not_commute_of_isTwin' hkf'' hf hfk e.symm
  have hcμ : f * f'' * f ∈ μ := by
    have := hμ.mul_mate_mul_mem hP hf''E (hμ.mate_notMem hP hf'E hf'μ hk hf'k) hf hf''f
    rwa [heq, Pair.mul_mul_eq hP hf''E hf hf''f] at this
  have hga : IsTwin E (f * g * f) (f * f' * f) := by
    have := isTwin_conj hP f hgf'
    rwa [Pair.inv_eq hP hf] at this
  have hka : f'' * (f * f' * f) ≠ f * f' * f * f'' := by
    intro h
    have h2 := (hga.2.2.2 _ hf''E).2 h
    have h3 := (hkf''.2.2.2 _ (Pair.mul_mul_mem hP hf hg)).2 h2.symm
    exact hc h3.symm
  have hid := Pair.affine_identity hP hf hf'E hf''E hff' hka
  apply hf'μ
  rw [hid]
  have ha := hμ.mul_mate_mul_mem hP hf hfμ hg hfg
  have hb := hμ.mul_mate_mul_mem hP hf'E hf'μ hk hf'k
  exact hμ.mul_mul_mem _ (hμ.mul_mul_mem _ ha _ hb) _ hcμ

end IsTwinSection
end O2Mod
end CFSG.Fischer.Classification
end
