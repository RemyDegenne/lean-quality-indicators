namespace OAI

noncomputable section

open scoped BigOperators

namespace HarmonicCounterexample.Certificate

lemma block2_count : (block2.map GroupCertificate.count).sum = 89679381593658382387289553249083634058495437460952893084 := by
  norm_num [block2,group49984,group49985,group49986,group49987,group49988,group49989,group49990,group49991,group49992,group49993]

end HarmonicCounterexample.Certificate
end
end OAI
