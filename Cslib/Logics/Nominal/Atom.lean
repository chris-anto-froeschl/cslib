/-
Copyright (c) 2024 Bas Spitters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Cslib.Init
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Basic.Countable.Defs

/-!
# Atoms for Nominal Sets

This file defines atoms, which are abstract names used in nominal set theory.
Atoms are represented as wrapped natural numbers, providing a countably infinite
supply of distinguishable names.

## Main definitions

* `Atom` - The type of atoms (wrapped naturals)
* `Atom.fresh` - Generate a fresh atom not in a given finite set

This file is ported from the `spitters/nominal-lean` repository.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598, the SSProve
  `Nominal/` layer this development ports.
* [SSProve Nominal Package](https://github.com/SSProve/ssprove)
-/

@[expose] public section

namespace Cslib.Logic.Nominal

/-- Atoms are abstract names, represented as wrapped natural numbers.
    This provides a countably infinite supply of distinguishable names. -/
structure Atom where
  /-- The natural number that identifies the atom. -/
  val : ℕ
  deriving DecidableEq, Hashable, Repr, Ord

namespace Atom

@[ext]
theorem ext {a b : Atom} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only [mk.injEq]; exact h

instance : Inhabited Atom := ⟨⟨0⟩⟩

/-- Coercion to natural numbers -/
instance : Coe Atom ℕ := ⟨Atom.val⟩

/-- Linear order on atoms inherited from naturals -/
instance : LinearOrder Atom :=
  LinearOrder.lift' Atom.val (fun _ _ h => Atom.ext h)

instance : OrderBot Atom where
  bot := ⟨0⟩
  bot_le a := Nat.zero_le a.val

/-- Atoms are countable -/
instance : Countable Atom := ⟨⟨Atom.val, fun _ _ h => Atom.ext h⟩⟩

/-- Constructor from natural number -/
def ofNat (n : ℕ) : Atom := ⟨n⟩

theorem ofNat_val (n : ℕ) : (ofNat n).val = n := rfl

theorem val_ofNat (a : Atom) : ofNat a.val = a := rfl

/-- Offset: one plus the maximum in a set, used for fresh generation -/
noncomputable def offset (s : Finset Atom) : ℕ :=
  if h : s.Nonempty then s.sup' h Atom.val + 1 else 0

/-- Fresh atom: the smallest atom not in the given set -/
noncomputable def fresh (s : Finset Atom) : Atom :=
  ⟨offset s⟩

/-- Fresh atom has value greater than all atoms in the set -/
theorem fresh_val_gt {s : Finset Atom} {a : Atom} (ha : a ∈ s) :
    a.val < (fresh s).val := by
  simp only [fresh, offset]
  have hne : s.Nonempty := ⟨a, ha⟩
  simp only [hne, ↓reduceDIte]
  have hle := Finset.le_sup' Atom.val ha
  omega

end Atom

end Cslib.Logic.Nominal
