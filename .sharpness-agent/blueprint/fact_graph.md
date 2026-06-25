# Fact graph for the Lean formalization

```mermaid
graph TD
  ZD[Z^d geometry: l1 norm, boxes, translation]
  Bonds[unoriented bonds and oriented boundaries]
  Paths[paths, connectivity, first/last exit]
  Clusters[finite clusters and cluster event supports]

  Bern[finite Bernoulli product probability]
  Local[local events and support extension]
  Indep[disjoint-support independence]
  Mono[increasing events and monotonicity in p]
  Russo[Lemma 1: closed-pivotal Russo]

  Phi[phi_p(S), pTilde, supremum facts]
  Shield[random shield set S(omega)]
  Diff[Lemma 2: fundamental differential inequality]
  ODE[ODE/log comparison]
  Super[Lemma 3: supercritical lower bound]
  Boundary[Lemma 4: boundary inequality]
  Subcrit[Lemma 5: subcritical exponential decay]
  Crit[theta, pCrit, pTilde = pCrit]
  Main[final sharpness theorem]

  ZD --> Bonds --> Paths --> Clusters
  Bern --> Local --> Indep
  Local --> Mono --> Russo
  Indep --> Russo
  Paths --> Phi
  Mono --> Phi
  Phi --> Shield --> Diff
  Paths --> Shield
  Indep --> Shield
  Russo --> Diff
  Diff --> ODE --> Super
  Clusters --> Boundary
  Indep --> Boundary
  Boundary --> Subcrit
  Phi --> Subcrit
  ZD --> Subcrit
  Super --> Crit
  Subcrit --> Crit --> Main
```

Critical hard nodes:

- `Russo`: prove in a generic finite Boolean product setting.
- `Shield`: prove deleted-internal-edge characterization and support separation.
- `Diff`: assemble Russo + pivotal equivalence + independence + finite sum decomposition.
- `Boundary`: cluster last-exit + three-event independence.
- `Crit`: handle endpoint `pTilde = 1` carefully.
