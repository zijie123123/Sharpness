/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.CriticalPoint

/-!
# Main Sharpness Theorem

This file states and proves the final sharpness theorem from the critical-point
lemmas.
-/

namespace Sharpness

/--
Sharpness for nearest-neighbor Bernoulli bond percolation on `Z^d`, stated using
finite box exit probabilities and `theta` as their decreasing-limit infimum.
-/
theorem sharpness_zd (d : Nat) (_hd : 2 <= d) :
    (forall p : Real, 0 <= p -> p < pCrit d ->
      exists c : Real, 0 < c /\
        forall n : Nat, boxExitProb d p n <= Real.exp (-(c * (n : Real)))) /\
    (forall p : Real, pCrit d < p -> p < 1 ->
      theta d p >= (p - pCrit d) / (p * (1 - pCrit d))) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num : (0 : Nat) < 2) _hd
  constructor
  · intro p hp0 hp
    exact exponential_decay_below_pCrit (d := d) (p := p) (hd := hdpos) (hp0 := hp0) (hp := hp)
  · intro p hp hp1
    exact supercritical_lower_bound_above_pCrit (d := d) (p := p) (hd := hdpos) (hp := hp)
      (hp1 := hp1)

end Sharpness
