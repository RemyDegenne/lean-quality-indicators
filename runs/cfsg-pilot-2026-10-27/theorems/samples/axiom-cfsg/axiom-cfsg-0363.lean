@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.SectionRank CFSG.SectionRank.Native

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

open scoped Matrix

theorem ksetCheck_parts :
    O.vmul ksetVectors[0]! Zn.1 < 2 ^ 112 ∧ ∀ i < ksetSize, ksetVectors[i]! < 2 ^ 112 ∧
      (ksetEdges[i]!)[0]! < ksetSize ∧
      ksetVectors[(ksetEdges[i]!)[0]!]! = O.vmul ksetVectors[i]! Xn.1 ∧
      (ksetEdges[i]!)[1]! < ksetSize ∧
      ksetVectors[(ksetEdges[i]!)[1]!]! = O.vmul ksetVectors[i]! Yn.1 ∧
      ksetVectors[i]! ≠ O.vmul ksetVectors[0]! Zn.1 :=
  ⟨kset_w_lt, kset_all⟩

end CFSG.Sporadic.J4Schreier
end
