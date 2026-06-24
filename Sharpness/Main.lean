import Sharpness.CriticalPoint

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
  constructor
  · intro p hp0 hp
    exact exponential_decay_below_pCrit (d := d) hp0 hp
  · intro p hp hp1
    exact supercritical_lower_bound_above_pCrit (d := d) hp hp1

end Sharpness
