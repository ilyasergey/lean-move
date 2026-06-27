/-
Axiom audit for the LeanMove type-soundness theorems.

Run from the project root, after `lake build` (or at least `lake build core`):

    lake env lean scripts/AxiomCheck.lean

Expected output (one line per theorem; ordering may vary):

    'type_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
    'type_soundness_dec' depends on axioms: [propext, Classical.choice, Quot.sound]

The three axioms are the standard classical axioms inherited from mathlib
(see ARTIFACT.md §6). The decisive point is that `sorryAx` does NOT appear:
its absence certifies that the soundness proofs contain no holes.

This file is intentionally not part of any `lake` build target; it is meant to
be run explicitly with `lake env lean` as a verification step.
-/
import LeanMove.Typing.TypeSoundness

open LeanMove.Typing.TypeSoundness

#print axioms type_soundness
#print axioms type_soundness_dec
