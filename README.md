# Formalizing Sharpness for Bernoulli Percolation

This repository formalizes the sharpness phase transition for Bernoulli bond
percolation on `Z^d`.

The formalization follows the argument of Hugo Duminil-Copin and Vincent
Tassion in
[*A new proof of the sharpness of the phase transition for Bernoulli
percolation on `\mathbb{Z}^d`*](https://arxiv.org/abs/1502.03051).

The development is written in Lean 4 and builds on mathlib. It defines the
finite-volume percolation model on `Z^d`, including bonds, paths, clusters,
finite Bernoulli product probabilities, local events, monotonicity,
independence, Russo's formula, and the differential inequalities used in the
Duminil-Copin--Tassion sharpness argument.

The final theorem is in [`Sharpness/Main.lean`](Sharpness/Main.lean). It proves
the two main sharpness conclusions. For \(p < p_c\), finite box exit
probabilities decay exponentially:

\[
\exists c > 0,\ \forall n,\quad
\operatorname{boxExitProb}(d,p,n) \le \exp(-c n).
\]

For \(p_c < p < 1\), the percolation density satisfies the mean-field lower
bound:

\[
\theta_d(p) \ge \frac{p - p_c}{p(1-p_c)}.
\]

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
