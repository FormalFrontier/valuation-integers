/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegersTest.Cauchy.UniformCompletionInputs
import ValuationIntegers.Cauchy.UniformCompletion

/-!
# Rational uses of the completion comparison

The comparison gives a limit for a rational Cauchy representative and takes the
coefficient three to a nonzero element of the uniform completion.
-/

noncomputable section

open scoped Topology

namespace CauSeq.Completion

open CauSeq.RationalCompletionInputs

private theorem tendsto_threeSeq :
    Filter.Tendsto (fun n : ℕ => ((threeSeq n : ℚ) : UniformSpace.Completion ℚ))
      Filter.atTop (𝓝 (equivUniformCompletion (mk threeSeq))) :=
  tendsto_coe_equivUniformCompletion_mk threeSeq

private theorem equivUniformCompletion_three_ne_zero :
    equivUniformCompletion
        (CauSeq.Completion.ofRat (abv := (norm : ℚ → ℝ)) (3 : ℚ)) ≠
      (0 : UniformSpace.Completion ℚ) := by
  simpa [zeroImage, threeImage] using zeroImage_ne_threeImage.symm

end CauSeq.Completion
