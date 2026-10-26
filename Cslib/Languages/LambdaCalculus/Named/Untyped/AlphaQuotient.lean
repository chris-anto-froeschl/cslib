/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivProperties

/-! # The α-quotiented λ-calculus `Λα` and the reduction system `λNα`

This file provides the *named* side of the isomorphism of

* Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*,
  TPHOLs 2007,

namely the type `Λα` of the paper's Section 2.1 and the reduction system `λNα` of its Table 1:
the quotient of the raw syntax `Λvar` by α-equivalence, with substitution and β-reduction
defined *directly on the quotient*.

Cslib already provides the raw syntax `Λvar` (`Named.Untyped.Term`), capture-avoiding
substitution on it, α-equivalence (`Term.AlphaEquiv`) and the proofs
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
  lifted from `Λvar` through the quotient. `TermAlpha.abs` is not injective.
* `BetaAlpha` : β-reduction of `λNα`, defined directly at the quotient level.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do
  Work*][Norrish2007a]
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped

/-- α-equivalence as a `Setoid`: two raw terms are identified when they differ only in the names
of their bound variables. -/
def Term.alphaSetoid (Var : Type u) [DecidableEq Var] [HasFresh Var] : Setoid (Term Var) where
  r := Term.AlphaEquiv
  iseqv := ⟨Term.AlphaEquiv.refl, Term.AlphaEquiv.symm, Term.AlphaEquiv.trans⟩

/-- `Λα` (Section 2.1 [Norrish2007a]): raw terms up to α-equivalence. -/
def TermAlpha (Var : Type u) [DecidableEq Var] [HasFresh Var] : Type u :=
  Quotient (Term.alphaSetoid Var)

namespace TermAlpha

/-- The α-equivalence class of a raw term. -/
def mk (m : Term Var) : TermAlpha Var := Quotient.mk (Term.alphaSetoid Var) m

@[inherit_doc] scoped notation "⟦" m "⟧α" => TermAlpha.mk m

/-- Two raw terms have the same class iff they are α-equivalent. -/
lemma mk_eq_mk {m n : Term Var} : (⟦m⟧α : TermAlpha Var) = ⟦n⟧α ↔ m =α n :=
  Quotient.eq

/-- Variables of `Λα`. -/
def var (x : Var) : TermAlpha Var := ⟦Term.var x⟧α

/-- Application in `Λα`, lifted from `Λvar`. -/
def app : TermAlpha Var → TermAlpha Var → TermAlpha Var :=
  Quotient.map₂ Term.app (fun _ _ h₁ _ _ h₂ => Term.AlphaEquiv.app h₁ h₂)

/-- Abstraction in `Λα`, lifted from `Λvar`. This operation is *not* injective. -/
def abs (x : Var) : TermAlpha Var → TermAlpha Var :=
  Quotient.map (Term.abs x) (fun _ _ h => Term.AlphaEquiv.abs_congr h)

/-- Capture-avoiding substitution on `Λα`, of type `Λα × V × Λα → Λα` as in Table 1
[Norrish2007a]. Well defined because substitution respects α-equivalence
(`Term.subst.preserve_AlphaEquiv`). -/
def subst (M : TermAlpha Var) (x : Var) (N : TermAlpha Var) : TermAlpha Var :=
  Quotient.map₂ (fun m n => m[x := n])
    (fun _ _ h₁ _ _ h₂ => Term.subst.preserve_AlphaEquiv h₁ h₂) M N

/-- Application on classes is application on representatives. -/
lemma app_mk (m n : Term Var) : app ⟦m⟧α ⟦n⟧α = ⟦Term.app m n⟧α := rfl

/-- Abstraction on classes is abstraction on representatives. -/
lemma abs_mk (x : Var) (m : Term Var) : abs x ⟦m⟧α = ⟦Term.abs x m⟧α := rfl

/-- Substitution on classes is substitution on representatives. -/
lemma subst_mk (m n : Term Var) (x : Var) :
    subst ⟦m⟧α x ⟦n⟧α = ⟦m[x := n]⟧α := rfl

/-- Induction principle for `Λα`: every element is the class of a raw term. -/
@[elab_as_elim] lemma ind {motive : TermAlpha Var → Prop} (h : ∀ m, motive ⟦m⟧α) (M) :
    motive M := Quotient.ind h M

end TermAlpha

/-- β-reduction of `λNα` (Table 1 [Norrish2007a]), on the α-quotiented type. The paper takes
its rules as known; these are the usual ones, as in HOL's `compat_closure beta`. Its de Bruijn
counterpart is Definition 7 (`DBeta'`), and Theorem 12 says that `f` maps one onto the other. -/
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

/-- η-reduction of `λNα`, used in Section 4.4 [Norrish2007a]. -/
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
