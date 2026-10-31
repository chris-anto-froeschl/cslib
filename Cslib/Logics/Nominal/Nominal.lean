/-
Copyright (c) 2024 Bas Spitters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import Cslib.Logics.Nominal.FinPerm

/-! # Supports

A finite set of atoms supports an element of a type with a permutation action if every
permutation that fixes the set pointwise fixes the element.

The permutation action uses Mathlib's `MulAction FinPerm α`. This file is ported from the
`spitters/nominal-lean` repository.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*,
  Cambridge University Press, 2013, Chapters 2-3.
-/

@[expose] public section

namespace Cslib.Logic.Nominal

/-- A set S supports an element x if every permutation fixing S pointwise
    also fixes x. -/
def Supports {α : Type*} [MulAction FinPerm α] (s : Finset Atom) (x : α) : Prop :=
  ∀ π : FinPerm, (∀ a ∈ s, π a = a) → π • x = x

end Cslib.Logic.Nominal
