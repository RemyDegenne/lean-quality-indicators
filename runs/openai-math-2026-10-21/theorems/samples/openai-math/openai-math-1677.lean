namespace OAI

noncomputable section

open Set Filter Real MeasureTheory

namespace GeneralMahler.SCal.SE

open Tag Grid Jet Profile Segment

variable (H:NG)(m:ℝ) {h:ℝ}

include H in
lemma CDa (hh:0<h)(he:h≤16/100):
    let v:=seg m h
    |ca0 v| ≤(321/1000)*h^2 ∧ |bd0 v|≤ (73/1000)*h^3 :=by
  intro v
  have hi:= chAbs m hh he testC (a:=95/100) (by positivity) fun x=> by
    apply abs_le.mpr; have hi:=hNC H x; norm_num at *; exact hi
  have hj:= chAbs m hh he (hqt H) (a:=56/100) (by positivity) fun x=>by
    apply abs_le.mpr
    have hq := hNQ H x
    norm_num at hq ⊢
    exact hq
  have hv:= (endDa H m hh).2
  constructor
  · have hc:ca0 v=bav Cp v-(Cp v.1+Cp v.2)/2:=by unfold ca0;ring
    rw [hc]; change |_| ≤ _ at hi; change |bav Cp _- _|≤_
    unfold v; nlinarith
  have he : bd0 v=(qu v.1-qu v.2)*(bav qu v-(qu v.1+qu v.2)/2):=by
    unfold bd0 qPlus mdis sqav
    rw [bav_sym (hqt H) v,bav_sym (sq_test (hqt H)) v]
    simp only [Prod.snd_swap]; ring
  rw [he,abs_mul,abs_sub_comm (qu v.1)]
  apply le_trans (mul_le_mul hv hj (abs_nonneg _) (by positivity))
  nlinarith [show 0≤h^3 by positivity]

end GeneralMahler.SCal.SE
end
end OAI
