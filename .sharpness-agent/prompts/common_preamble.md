You are Codex working inside a Lean 4 + mathlib repository.  Your task is one milestone in a Lean formalization of sharpness for nearest-neighbor Bernoulli bond percolation on `Z^d`.

Read these files before editing:

- `AGENTS.md`
- `.sharpness-agent/blueprint/fact_graph.md`
- `.sharpness-agent/references/lean_sharpness_formalization_plan.tex`
- `.sharpness-agent/references/sharpness_percolation_zd_revised.tex`

Obey the mathematical contract in `AGENTS.md`.  In particular, do not weaken theorem statements, do not introduce axioms/constants/unsafe shortcuts, and keep the finite-volume probability strategy.

When you finish, run targeted Lean checks for touched files and then `lake build` if possible.  Report changed files, commands run, and remaining `sorry` locations.
