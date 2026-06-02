# Assignment 2: Formalizing a Proof with a Lean Proving Agent

**Course:** DSA5210 AI for Mathematics  
**Canvas course:** 93088  
**Canvas assignment:** 253513  
**Weight:** 20%  
**Points:** 100  
**Due:** Friday, 12 June 2026, 23:59 Singapore time  
**Submission:** online file upload, restricted to `.lean`, `.md`, `.pdf`, and `.zip`  
**Status on Canvas:** draft (unpublished — being finalized)

## Task

Use an agentic coding assistant — such as Claude, Codex, opencode, or openclaw — to
obtain, set up, and drive a **Lean proving agent** that formalizes a mathematical
theorem in **Lean 4 with Mathlib**, iterating until the **Lean kernel** accepts the
proof with **no `sorry`** and no errors.

You **drive the agent with natural-language prompts**; the agent sets up the Lean
project, writes the Lean code, and checks it against the kernel. You do not need to
write the proof tactics by hand.

**Recommended:** formalize the theorem you proved in **Assignment 1** (your
`blueprint.md`). You already have a complete, human-readable natural-language proof;
Assignment 2 turns that same proof into a machine-checked Lean proof. You may instead
choose another precise theorem if you prefer, subject to the same standard below.

## Lean proving agents

Suitable Lean agent systems include **numina-lean-agent** and **Archon**. Both launch a
coding agent (Claude Code) in a loop that writes Lean and verifies it with the Lean
kernel through `lean-lsp-mcp`. These harnesses are **agent-agnostic**: because they
drive a coding assistant, they are easy to repoint at another agent (Codex, opencode,
…). You may use any Lean proving agent you can install and run; part of the task is
using a coding assistant to figure out the setup.

Worked examples from class (Euler's partition theorem, formalized two ways, with
in-browser Lean links):

- https://jiajunma.github.io/dsa5210/numina/ (Numina) ·
  https://jiajunma.github.io/dsa5210/rethlas-archon/ (Archon)
- https://jiajunma.github.io/dsa5210/euler-lean/ (the Lean proofs + live editor)

## What "done" means

- A Lean 4 file (or a small `lake` project) that **compiles against Mathlib with no
  errors and no `sorry`**.
- The formal **statement faithfully matches your theorem**. State it honestly: a
  machine-checked proof of a weakened or trivially-true restatement earns little
  credit.
- `#print axioms <your_theorem>` shows only the standard axioms (some subset of
  `propext`, `Classical.choice`, `Quot.sound`) — in particular **no `sorryAx`** and no
  custom `axiom`.
- *Optional bonus:* keep the definitions **computable** (definitions reduce under
  `#eval`), and note if you obtain a choice-free proof (`#print axioms` =
  `[propext, Quot.sound]`).

## Required submission files

- `Formalization.lean` — your Lean formalization (sorry-free, compiles against
  Mathlib). If you used a multi-file `lake` project, submit a `.zip` of the project (or
  the main files).
- `report.pdf` (about 2–4 pages) containing:
  - the theorem, stated both **informally** and as the **Lean `theorem`**;
  - which Lean agent/system you used and **how you drove it — include the actual
    natural-language prompts you gave**;
  - a short account of the run: how many rounds/iterations, what the agent did, and
    where you had to steer, constrain, or repair it;
  - the final **`#print axioms`** output for your main theorem;
  - a brief reflection: what the agent formalized well, what was hard, and what you
    learned about autoformalization.
- *Optional:* the agent's config / prompt files, or a shareable link to your proof
  (e.g. a `live.lean-lang.org` link).

## Expected workflow

1. Choose your theorem — recommended: your Assignment 1 result. Write a clean,
   self-contained statement (all definitions and hypotheses included).
2. Use a coding assistant to obtain, inspect, and set up a Lean proving agent: a Lean 4
   + Mathlib project and the agent's loop.
3. Seed the Lean **statement** (with `sorry`) and drive the agent to fill in the proof.
   Verify after each step with the Lean kernel (`lean_diagnostic_messages` /
   `lake env lean`), not by eye.
4. Iterate until the file is sorry-free and error-free; then check `#print axioms`.
5. Write the report.

## Scope and honesty

- A faithful formalization of a **nontrivial but realistic** theorem. It is fine if the
  theorem you formalize is smaller than your full Assignment 1 proof — fully
  formalizing even one clean lemma or a self-contained theorem is substantial work.
- **Do not pad with `sorry`** or hidden `axiom`s; the kernel check and `#print axioms`
  are how this is verified.
- The Lean statement must genuinely express your theorem. If in doubt about whether a
  statement is faithful, explain your choice in the report.

## Grading (100 points)

| Criterion | Points |
|---|---|
| Faithful, nontrivial **formal statement** of the theorem | 25 |
| **Sorry-free, kernel-checked** proof; clean `#print axioms` | 40 |
| Effective, well-documented use of a **Lean agent** (prompts + run account) | 20 |
| Report clarity and reflection | 15 |
| *Bonus:* computable / choice-free formalization | up to +5 |

Submit exactly your Lean file(s) and `report.pdf` (plus any optional config/links).
