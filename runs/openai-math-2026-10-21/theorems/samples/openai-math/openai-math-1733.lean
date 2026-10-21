namespace OAI

noncomputable section

open Set Filter Real MeasureTheory MeasureTheory.Measure

open scoped Topology Interval

namespace GeneralMahler.SCal.SE

open Tag Grid Profile Jet

local notation "w" => Profile.omegaP

variable {h:ℝ}

lemma ubP (hh:0<h): 0<ubase h:=by unfold ubase; have hi:=wp_pos; positivity

end GeneralMahler.SCal.SE
end
end OAI
