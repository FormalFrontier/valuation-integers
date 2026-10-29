/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib
import ValuationIntegers.HeightOne.ScalarTower

/-!
# Coefficient-field triviality and rational-function valuations

Installing coefficient-field triviality as a local instance allows Mathlib's
rational-function valuation classifier to apply to a height-one valuation.
-/

universe u

example {F : Type u} [Field F] [DecidableEq (RatFunc F)]
    (p : IsDedekindDomain.HeightOneSpectrum (Polynomial F)) :
    Xor (Valuation.IsEquiv
      (IsDedekindDomain.HeightOneSpectrum.valuation (RatFunc F) p)
      (RatFunc.inftyValuation F))
      (∃! q : IsDedekindDomain.HeightOneSpectrum (Polynomial F),
        Valuation.IsEquiv
          (IsDedekindDomain.HeightOneSpectrum.valuation (RatFunc F) p)
          (IsDedekindDomain.HeightOneSpectrum.valuation (RatFunc F) q)) := by
  let : Valuation.IsTrivialOn F
      (IsDedekindDomain.HeightOneSpectrum.valuation (RatFunc F) p) :=
    IsDedekindDomain.HeightOneSpectrum.valuation_isTrivialOn p
  exact RatFunc.valuation_isEquiv_infty_or_adic
