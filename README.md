# Formalizing Sharpness for Bernoulli Percolation

This repository formalizes the sharpness phase transition for Bernoulli bond percolation on `Z^d`.

The development is written in Lean 4 and builds on mathlib. It defines the
finite-volume percolation model on `Z^d`, including bonds, paths, clusters,
finite Bernoulli product probabilities, local events, monotonicity,
independence, Russo's formula, and the differential inequalities used in the
Duminil-Copin--Tassion sharpness argument.

The final theorem is in [`Sharpness/Main.lean`](Sharpness/Main.lean). It proves
the two main sharpness conclusions:

* below the critical point, finite box exit probabilities decay exponentially;
* above the critical point, the percolation density satisfies the mean-field
  lower bound.

The Lean development currently has about 6.2k lines of Lean code. The checked
Lean files contain no `sorry` and introduce no user-defined `axiom` declarations.

## Workflow Report

A summary of the formalization workflow is available in
[`Report.pdf`](https://github.com/zijie123123/Sharpness/blob/main/Report.pdf).

## Download and Verify

Clone the repository:

```bash
git clone https://github.com/zijie123123/Sharpness.git
cd Sharpness
```

Fetch the mathlib cache, if available:

```bash
lake exe cache get
```

Build the project:

```bash
lake build
```

To check the main import file directly:

```bash
lake env lean Sharpness.lean
```

The main theorem itself is located in:

```text
Sharpness/Main.lean
```
