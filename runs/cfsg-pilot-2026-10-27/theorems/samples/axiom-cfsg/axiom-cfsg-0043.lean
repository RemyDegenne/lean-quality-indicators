public section

open scoped MatrixGroups Matrix

namespace CFSG.ASVolI.ChH.GL

open CFSG.LocalAnalysis.ComponentInitial

theorem glEquivProj_apply (n : ℕ) (X : GL (Fin n) (ZMod 2)) :
    glEquivProj n X = LinearFlag.proj n (ZMod 2) (glEquivSL n X) := rfl

end CFSG.ASVolI.ChH.GL
end
