/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivDefs
public import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties

/-! # Properties of the swap (transposition) operation on lambda terms

Helper lemmas for reasoning about `Term.swap` and its interaction with
`AlphaEquiv`, `rename`, `vars`, and `fv`.

The notion of *atom swapping* (transposition) as the basis for defining α-equivalence
originates from [Gabbay and Pitts, *A New Approach to Abstract Syntax with Variable
Binding*][Gabbay2002] (Section 2, page 3). The key observation is that α-equivalence can
be defined using the notion of atom swapping in lieu of the traditional
renaming/substitution approach.

The swap (transposition) operation `m.swap x y` implements the permutation action
`(x y) · E` from [Crole2012] (Section 2). It simultaneously replaces all occurrences
of `x` with `y` and vice versa throughout a term.

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012], Sections 2 and 6
* [M. Gabbay and A. Pitts, *A New Approach to Abstract Syntax with Variable
  Binding*][Gabbay2002], Section 2
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.Named.Untyped.Term

end LambdaCalculus.Named.Untyped.Term

end Cslib
