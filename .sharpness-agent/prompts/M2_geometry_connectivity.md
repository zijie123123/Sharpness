# Milestone M2: geometry, bonds, paths, connectivity, clusters

Focus files:

- `Sharpness/Zd.lean`
- `Sharpness/Bonds.lean`
- `Sharpness/FiniteGeometry.lean`
- `Sharpness/Paths.lean`
- `Sharpness/Clusters.lean`
- `Sharpness/Events.lean`

Goal: build the deterministic combinatorial layer used by the probability arguments.

Required results:

1. Vertex type for `Z^d`, `l1` norm, adjacency, zero vertex, translations.
2. Finite boxes `Lambda n` / `ball d n` and membership lemmas.
3. Translation invariance of adjacency and paths.
4. The key subcritical geometry lemma:
   if `y ∈ Lambda L` and `z ∉ Lambda n`, then `z - y ∉ Lambda (n - L)` for `n >= L`.
   Prove this by the `l1` triangle inequality, preferably via the contrapositive.
5. Unoriented bonds plus oriented boundary edges `(x,y)` with `x ∈ S`, `y ∉ S`, `x ∼ y`.
6. Internal bonds, exit/boundary bonds, and boundary endpoint bound: if `S ⊆ Lambda (L-1)` and `(x,y) ∈ ∂E S`, then `y ∈ Lambda L`.
7. List paths, path validity, open paths, path-in-set, connectivity inside a finite set.
8. First-exit and last-exit lemmas for a path crossing from a set to its complement.
9. Locality and increasingness of connection and finite exit events.
10. Finite cluster `C_S(u)` and cluster event support: `C_S(u)=C0` depends only on internal `S`-edges incident to `C0`.

Implementation hints:

- Keep the graph library minimal.  Lists are enough.
- For `l1`, use a `Finset.univ.sum` of absolute values; if `Nat` coercions cause pain, create helper lemmas early.
- Boundary edges can remain oriented even if percolation configurations use unoriented bonds.
- If the exact cluster support proof is hard, write the theorem with the exact statement and leave a localized `sorry`; do not weaken it to all internal edges, since Lemma 4 needs the sharper support.

Run:

```bash
lake env lean Sharpness/Zd.lean
lake env lean Sharpness/Bonds.lean
lake env lean Sharpness/FiniteGeometry.lean
lake env lean Sharpness/Paths.lean
lake env lean Sharpness/Clusters.lean
lake env lean Sharpness/Events.lean
lake build
```
