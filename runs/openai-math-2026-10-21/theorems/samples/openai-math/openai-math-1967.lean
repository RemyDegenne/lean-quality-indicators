namespace OAI

namespace SharpPlanar.Numerical

open IntegerIntervals IntegerBasis IntegerGrid CachedData

lemma lentry0_2_contains : lentry0_2.Contains (Lmat 0 2) := by
  have h0 := K_column_contains (n:=node4) (m:=7) (by decide) (by decide) false false cm4_7_0_0.contains
  have h1 := K_column_contains (n:=node4) (m:=7) (by decide) (by decide) false true cm4_7_0_1.contains
  have hh := S_column_value_contains (m:=node7) h0
  change lentry0_2.Contains (S (columnVector node4 false) (node7,false))
  convert hh using 1
  decide +kernel

end SharpPlanar.Numerical
end OAI
