/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Haoxuan Yin, Chris Anto Fröschl
-/

import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic
import Cslib.Languages.LambdaCalculus.Named.Untyped.RenameProperties
import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivProperties
import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivVariants.Equalities
import Cslib.Languages.LambdaCalculus.NamedDeBruijn.Isomorphism
import Cslib.Languages.LambdaCalculus.NamedDeBruijn.Transfer

/-! # λ-calculus

Tests for the named untyped λ-calculus, and a worked example for the five characterizations of
α-equivalence of [Crole2012] and the isomorphism with de Bruijn terms of [Norrish2007a]: the three
operations on atoms, the five relations on one pair of terms, the counterexamples of
Proposition 4.3, and one β-step on both sides of the isomorphism.

-/

namespace CslibTests

open Cslib Cslib.LambdaCalculus.Named.Untyped.Term

def x := 0
def y := 1
def z := 2
def w := 3

def lambdaId := abs x (var x)

example : (abs x (var x)) =α (abs y (var y)) := by
  have h : (abs y (var y)) = (abs y ((var x).rename x y)) := by grind [rename]
  rw [h]
  apply AlphaEquiv.abs_rename
  simp only [vars]
  decide

example : (abs y (var x)).subst x (app (var y) (var z)) = (abs w (app (var y) (var z))) := by
  simp only [rename, subst, fv, vars]
  decide

-- section 5.3.4 of TAPL
example : (abs y (app (var x) (var y))).subst x (app (var y) (var z)) =
    (abs w (app (app (var y) (var z)) (var w))) := by
  simp only [subst, vars, rename]
  decide

example : (abs x (abs y (app (var x) (var y)))) =α (abs y (abs x (app (var y) (var x)))) := by
  apply AlphaEquiv.abs (y := z)
  · simp only [vars]
    decide
  simp only [rename]
  apply AlphaEquiv.abs (y := w)
  · simp only [vars]
    decide
  simp only [rename]
  apply AlphaEquiv.refl

end CslibTests

namespace CslibTests.AlphaEquivalence

open Cslib.Logic.Nominal

-- Atoms are wrapped natural numbers; `a b c d z` are `0 1 2 3 4`.
abbrev a : Atom := ⟨0⟩
abbrev b : Atom := ⟨1⟩
abbrev c : Atom := ⟨2⟩
abbrev d : Atom := ⟨3⟩
abbrev z : Atom := ⟨4⟩

section Named

open Cslib Cslib.LambdaCalculus.Named.Untyped Cslib.LambdaCalculus.Named.Untyped.Term

-- The running example `M = λa. a b` and an α-equivalent term `N = λc. c b`.
abbrev M : Term Atom := abs a (app (var a) (var b))
abbrev N : Term Atom := abs c (app (var c) (var b))

-- Renaming identifies `a` and `b`: `λb. b b`, the free `b` is captured.
example : M.rename a b = abs b (app (var b) (var b)) := by decide

-- The swap exchanges `a` and `b`: `λb. b a`.
example : M.swap a b = abs b (app (var b) (var a)) := by decide

-- Substitution replaces only the free `b`, renaming the binder to the fresh `c`: `λc. c a`.
example : M.subst b (var a) = abs c (app (var c) (var a)) := by
  simp only [subst, rename, fv, vars]
  decide

-- `∼p` (Definition 3.1, CSLib's `=α`): rule `pi` with witness `d`.
theorem M_alphaEquiv_N : M =α N :=
  AlphaEquiv.abs (y := d) (by decide) (.app .var .var)

-- The other four relations, from Crole's theorems ...
example : AlphaEquivPFresh M N := (alphaEquiv_iff_alphaEquivPFresh M N).mp M_alphaEquiv_N
example : AlphaEquivP1 M N := (alphaEquiv_iff_alphaEquivP1 M N).mp M_alphaEquiv_N
example : AlphaEquivR M N := (alphaEquiv_iff_alphaEquivR M N).mp M_alphaEquiv_N
example : AlphaEquivRFresh M N := (alphaEquiv_iff_alphaEquivRFresh M N).mp M_alphaEquiv_N

-- ... and directly with each relation's own rule: `pi#` and `pi1` with the witness `d`, and the
-- renaming axioms `α` and `α#` renaming `a` to `c` in one step.
example : AlphaEquivPFresh M N := AlphaEquivPFresh.abs (y := d) (by decide) (.app .var .var)
example : AlphaEquivP1 M N := AlphaEquivP1.abs (y := d) (by decide) (.app .var .var)
example : AlphaEquivR M N := by
  have h := AlphaEquivR.alpha (x := a) (x' := c) (m := app (var a) (var b)) (by decide)
  simpa [subst] using h
example : AlphaEquivRFresh M N := by
  have h := AlphaEquivRFresh.alpha (x := a) (x' := c) (m := app (var a) (var b)) (by decide)
  simpa [subst] using h

-- Proposition 4.3, with only `z ∉ {a, b}`: `λa. a z ∼²p λb. b a` with witness `z` ...
example : AlphaEquivP2 (abs a (app (var a) (var z))) (abs b (app (var b) (var a))) :=
  AlphaEquivP2.abs (z := z) (by decide) (.app .var .var)

-- ... but the free atoms differ, so the two terms are not α-equivalent.
example : ¬ ((abs a (app (var a) (var z))) =α (abs b (app (var b) (var a)))) := fun h => by
  have := h.same_fv
  revert this
  decide

-- With no side condition: `λa. b a ∼³p λb. a b` with witness `b`, again not α-equivalent.
example : AlphaEquivP3 (abs a (app (var b) (var a))) (abs b (app (var a) (var b))) :=
  AlphaEquivP3.abs (z := b) (.app .var .var)

example : ¬ ((abs a (app (var b) (var a))) =α (abs b (app (var a) (var b)))) := fun h => by
  have := h.same_fv
  revert this
  decide

end Named

section DeBruijn

open Cslib.LambdaCalculus.Unscoped.Untyped Cslib.LambdaCalculus.Unscoped.Untyped.Term
open Cslib.LambdaCalculus.NamedDeBruijn
open Cslib.LambdaCalculus.Named.Untyped (TermAlpha BetaAlpha)
open scoped Cslib.LambdaCalculus.Named.Untyped.TermAlpha

-- `f` sends `λa. a b` and `λc. c b` to the same de Bruijn term: the bound atom becomes index 0,
-- the free `b` (atom 1) becomes index 2 under one binder.
example : fromTerm (.abs a (.app (.var a) (.var b))) = abs (app (var 0) (var 2)) := by decide
example : fromTerm (.abs c (.app (.var c) (.var b))) = abs (app (var 0) (var 2)) := by decide

-- In general, `f (λx. x y) = λ. 0 (ŷ + 1)` for distinct atoms `x` and `y`.
example (x y : Atom) (h : x ≠ y) :
    fromTerm (.abs x (.app (.var x) (.var y))) = abs (app (var 0) (var (y.val + 1))) := by
  simpa [Term.dLAM, Term.dsub, Term.lift] using fun e => h (Atom.ext e.symm)

-- `λb. b a` is a different term.
example : fromTerm (.abs b (.app (.var b) (.var a))) = abs (app (var 0) (var 1)) := by decide

-- Equal images decide α-equivalence (Theorem 11).
example : (.abs a (.app (.var a) (.var b)) : Lam) =α (.abs c (.app (.var c) (.var b))) :=
  fromTerm_alphaEquiv_iff.mp (by decide)

-- `f` on the quotient `Λα` is the bijection `dbEquiv`.
example : dbEquiv ⟦.abs a (.app (.var a) (.var b))⟧α = abs (app (var 0) (var 2)) := by decide

-- A β-step on the named side, `(λa. a b) c →β c b` in `Λα`, ...
theorem named_beta_step : BetaAlpha ⟦.app (.abs a (.app (.var a) (.var b))) (.var c)⟧α
    ⟦.app (.var c) (.var b)⟧α := by
  have h := BetaAlpha.red a ⟦.app (.var a) (.var b)⟧α ⟦.var c⟧α
  simpa [TermAlpha.abs_mk, TermAlpha.app_mk, TermAlpha.subst_mk,
    Cslib.LambdaCalculus.Named.Untyped.Term.subst] using h

-- ... and the corresponding `→d` step `(λ. 0 2) 2 →d 2 1` on de Bruijn terms, by Theorem 20.
example : Beta (app (abs (app (var 0) (var 2))) (var 2)) (app (var 2) (var 1)) :=
  betaAlpha_iff_beta.mp named_beta_step

-- Theorem 20 as a relation isomorphism, and Church-Rosser for `→β` on `Λα` transported from it.
noncomputable example : BetaAlpha (Var := Atom) ≃r Beta := dbRelIso
example : Relation.Confluent (BetaAlpha (Var := Atom)) := churchRosser_betaAlpha

end DeBruijn

end CslibTests.AlphaEquivalence
