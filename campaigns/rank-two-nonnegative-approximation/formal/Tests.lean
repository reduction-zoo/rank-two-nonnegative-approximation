import Challenge
open RankTwoNonnegativeApproximation
example : legalTarget ⟨1,1,[[1]],0⟩ = true := by native_decide
example : legalTarget ⟨1,1,[[-1]],0⟩ = false := by native_decide
example : squaredError ⟨1,1,[[3]],0⟩ [[1,1]] [[1],[1]] = 1 := by norm_num [squaredError, realEntry]
