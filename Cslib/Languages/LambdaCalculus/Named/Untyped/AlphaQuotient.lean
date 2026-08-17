/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivEquiv

/-! # The α-quotiented λ-calculus `Λα` and the reduction system `λNα`

This file provides the *named* side of the isomorphism of

* Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*,
  TPHOLs 2007,

namely the type `Λα` of the paper's Section 2.1 and the reduction system `λNα` of its Table 1:
the quotient of the raw syntax `Λvar` by α-equivalence, with substitution and β-reduction
defined *directly on the quotient* (as in Norrish [12] and Pitts [14]).

Cslib already provides the raw syntax `Λvar` (`Named.Untyped.Term`), capture-avoiding
substitution on it, α-equivalence (`Term.AlphaEquiv`, Definition 3.1 of Crole) and the proofs
that α-equivalence is an equivalence relation and is respected by substitution.  What is added
here is only the quotient packaging:

| Paper                | Cslib                    |
|----------------------|--------------------------|
| `Λvar`               | `Term Var`               |
| `=α`                 | `Term.AlphaEquiv`        |
| `Λα`                 | `TermAlpha Var`          |
| `VAR v`              | `TermAlpha.var v`        |
| `APP M N`            | `TermAlpha.app M N`      |
| `LAM v M`            | `TermAlpha.abs v M`      |
| `M[v := N]`          | `TermAlpha.subst M v N`  |
| `→β` of `λNα`        | `BetaAlpha`              |

## Main definitions

* `Term.alphaSetoid`, `TermAlpha` : the type `Λα`.
* `TermAlpha.var`, `TermAlpha.app`, `TermAlpha.abs`, `TermAlpha.subst` : the operations of `Λα`,
  obtained by lifting the corresponding operations of `Λvar` through the quotient.  Note that
  `TermAlpha.abs` is *not* injective, which is precisely the reason the paper needs
  Pitts-style recursion (or, here, a lifting argument) to define the map into `dB`.
* `BetaAlpha` : β-reduction of `λNα`, defined directly at the quotient level.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*][NV2007]
* [Michael Norrish, *Mechanising λ-calculus using a classical first order theory of terms with
  permutations*][Norrish2006]
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped

/-- α-equivalence, packaged as a `Setoid` (the underlying equivalence relation is
`Term.AlphaEquiv`, i.e. Definition 3.1 of Crole; the three components are `AlphaEquiv.refl`,
`AlphaEquiv.symm` and `AlphaEquiv.trans`). -/
def Term.alphaSetoid (Var : Type u) [DecidableEq Var] [HasFresh Var] : Setoid (Term Var) where
  r := Term.AlphaEquiv
  iseqv := ⟨Term.AlphaEquiv.refl, Term.AlphaEquiv.symm, Term.AlphaEquiv.trans⟩

/-- `Λα`: the α-quotient of the raw syntax `Λvar` (paper, Section 2.1). -/
def TermAlpha (Var : Type u) [DecidableEq Var] [HasFresh Var] : Type u :=
  Quotient (Term.alphaSetoid Var)

namespace TermAlpha

/-- The α-equivalence class of a raw term. -/
def mk (m : Term Var) : TermAlpha Var := Quotient.mk (Term.alphaSetoid Var) m

@[inherit_doc] scoped notation "⟦" m "⟧α" => TermAlpha.mk m

theorem mk_eq_mk {m n : Term Var} : (⟦m⟧α : TermAlpha Var) = ⟦n⟧α ↔ m =α n :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Variables of `Λα`. -/
def var (x : Var) : TermAlpha Var := ⟦Term.var x⟧α

/-- Application in `Λα`, lifted from `Λvar`. -/
def app : TermAlpha Var → TermAlpha Var → TermAlpha Var :=
  Quotient.map₂ Term.app (fun _ _ h₁ _ _ h₂ => Term.AlphaEquiv.app h₁ h₂)

/-- Abstraction in `Λα`, lifted from `Λvar`.  This operation is *not* injective. -/
def abs (x : Var) : TermAlpha Var → TermAlpha Var :=
  Quotient.map (Term.abs x) (fun _ _ h => Term.AlphaEquiv.abs_congr h)

/-- Capture-avoiding substitution on `Λα` (Table 1: for `λNα`, substitution has type
`Λα × V × Λα → Λα`).  Well defined by `Term.subst.preserve_AlphaEquiv`. -/
def subst (M : TermAlpha Var) (x : Var) (N : TermAlpha Var) : TermAlpha Var :=
  Quotient.map₂ (fun m n => m[x := n])
    (fun _ _ h₁ _ _ h₂ => Term.subst.preserve_AlphaEquiv h₁ h₂) M N

@[simp] theorem app_mk (m n : Term Var) : app ⟦m⟧α ⟦n⟧α = ⟦Term.app m n⟧α := rfl

@[simp] theorem abs_mk (x : Var) (m : Term Var) : abs x ⟦m⟧α = ⟦Term.abs x m⟧α := rfl

@[simp] theorem subst_mk (m n : Term Var) (x : Var) :
    subst ⟦m⟧α x ⟦n⟧α = ⟦m[x := n]⟧α := rfl

/-- Induction principle for `Λα`: every element is the class of a raw term. -/
@[elab_as_elim] theorem ind {motive : TermAlpha Var → Prop} (h : ∀ m, motive ⟦m⟧α) (M) :
    motive M := Quotient.ind h M

end TermAlpha

/-- β-reduction of `λNα` (paper, Table 1): defined directly on the α-quotiented type, with the
contraction rule using the quotient-level substitution. -/
inductive BetaAlpha : TermAlpha Var → TermAlpha Var → Prop where
  /-- Contraction of a β-redex. -/
  | red (x : Var) (M N : TermAlpha Var) :
      BetaAlpha (TermAlpha.app (TermAlpha.abs x M) N) (TermAlpha.subst M x N)
  /-- Congruence in the left argument of an application. -/
  | appL {M N : TermAlpha Var} (Z : TermAlpha Var) :
      BetaAlpha M N → BetaAlpha (TermAlpha.app M Z) (TermAlpha.app N Z)
  /-- Congruence in the right argument of an application. -/
  | appR {M N : TermAlpha Var} (Z : TermAlpha Var) :
      BetaAlpha M N → BetaAlpha (TermAlpha.app Z M) (TermAlpha.app Z N)
  /-- Congruence under an abstraction. -/
  | abs {M N : TermAlpha Var} (x : Var) :
      BetaAlpha M N → BetaAlpha (TermAlpha.abs x M) (TermAlpha.abs x N)

@[inherit_doc] scoped infix:39 " →βα " => BetaAlpha

/-- η-reduction of `λNα`, used in Section 4.4 of the paper. -/
inductive EtaAlpha : TermAlpha Var → TermAlpha Var → Prop where
  /-- Contraction of an η-redex `LAM x (APP M (VAR x))` with `x` not free in `M`. -/
  | red (x : Var) (m : Term Var) : x ∉ m.fv →
      EtaAlpha (TermAlpha.abs x (TermAlpha.app (TermAlpha.mk m) (TermAlpha.var x)))
        (TermAlpha.mk m)
  /-- Congruence in the left argument of an application. -/
  | appL {M N : TermAlpha Var} (Z : TermAlpha Var) :
      EtaAlpha M N → EtaAlpha (TermAlpha.app M Z) (TermAlpha.app N Z)
  /-- Congruence in the right argument of an application. -/
  | appR {M N : TermAlpha Var} (Z : TermAlpha Var) :
      EtaAlpha M N → EtaAlpha (TermAlpha.app Z M) (TermAlpha.app Z N)
  /-- Congruence under an abstraction. -/
  | abs {M N : TermAlpha Var} (x : Var) :
      EtaAlpha M N → EtaAlpha (TermAlpha.abs x M) (TermAlpha.abs x N)

@[inherit_doc] scoped infix:39 " →ηα " => EtaAlpha

end LambdaCalculus.Named.Untyped

end Cslib
