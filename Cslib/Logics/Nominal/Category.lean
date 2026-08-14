/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import Cslib.Logics.Nominal.Category.Nominal
public import Cslib.Logics.Nominal.Category.NominalMonoidal
public import Cslib.Logics.Nominal.Category.NominalMonoidalClosed
public import Cslib.Logics.Nominal.Category.NominalMonoidalClosedFull
public import Cslib.Logics.Nominal.Category.NominalMonoidalClosedComplete
public import Cslib.Logics.Nominal.Category.NominalSeparatedExp
public import Cslib.Logics.Nominal.Category.NominalAbstraction
public import Cslib.Logics.Nominal.Category.NominalCoreBridge
public import Cslib.Logics.Nominal.Category.NominalCoreEquivalence
public import Cslib.Logics.Nominal.Category.NominalCoreEquivalenceComplete
public import Cslib.Logics.Nominal.Category.NominalAbstractionClosed
public import Cslib.Logics.Nominal.Category.NominalAbstractionAdjunction
public import Cslib.Logics.Nominal.Category.NominalAbstractionNatIso
public import Cslib.Logics.Nominal.Category.NominalAbstractionRecursion

/-!
# The category of nominal sets

The categorical (Schanuel-topos) layer over the core nominal-sets development:
the category of nominal sets, its symmetric-monoidal and monoidal-closed
structure, the internal separated exponential, atom abstraction `[𝔸](−)` with its
binding adjunction and recursion principle, and the equivalence with the core
finitely-supported `FinPerm`-sets. Depends only on mathlib and `Nominal.*`.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*,
  Cambridge University Press, 2013.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598.
-/

@[expose] public section
