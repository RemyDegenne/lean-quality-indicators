namespace OAI

noncomputable section

open scoped BigOperators lp

namespace AtomicTriangular.Construction

open AtomicTriangular.Schur

lemma splitQ_lt (e : Fin 2) : splitQ e<1 := by fin_cases e <;> norm_num [splitQ,splitN,beta,delta]

end AtomicTriangular.Construction
end
end OAI
