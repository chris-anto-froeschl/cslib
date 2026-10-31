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
import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaQuotientProperties

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

-- Renaming replaces every occurrence of `a`, the binder included: `λb. b b`.
example : M.rename a b = abs b (app (var b) (var b)) := by
  -- `rename` compares each atom with `a`.
  rw [rename, rename, rename, rename]
  -- Both `a`s become `b`; the free `b` stays `b` either way, so it is captured.
  rw [ite_eq_left rfl, ite_self]

-- The swap `(a b)` exchanges `a` and `b` everywhere: `λb. b a`.
example : M.swap a b = abs b (app (var b) (var a)) := by
  -- A swap is the permutation `Equiv.swap a b` applied to every atom.
  rw [swap, permute, permute, permute, permute]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right]

-- Substitution `M[b := a]` replaces only the free `b`, renaming the binder first: `λc. c a`.
example : M.subst b (var a) = abs c (app (var c) (var a)) := by
  rw [subst]
  -- The binder `a` is not `b`, but it is free in `var a`, so it would capture `a`.
  rw [ite_eq_right (by decide : a ≠ b), ite_eq_right (by simp [fv])]
  -- So the binder is renamed to a fresh atom, the successor of the largest atom around: `c`.
  have hfresh : fresh (((var a).app (var b)).vars ∪ (var a).vars ∪ {b, a}) = c := by decide
  -- Renaming `a` to `c` in the body gives `c b`, and substituting there gives `c a`.
  have hren : ((var a).app (var b)).rename a c = (var c).app (var b) := by decide
  have hsub : ((var c).app (var b)).subst b (var a) = (var c).app (var a) := by
    rw [subst, subst, subst, ite_eq_right (by decide : c ≠ b), ite_eq_left rfl]
  simp only [hfresh, hren, hsub]

-- `∼p` (Definition 3.1, CSLib's `=α`) relates `M` and `N` by the rule `pi`.
theorem M_alphaEquiv_N : M =α N := by
  -- Choose the witness `d`, which occurs in neither term and differs from both binders.
  apply AlphaEquiv.abs (y := d)
  · simp only [vars]
    decide
  -- Renaming `a` and `c` to `d` gives the same body `d b` on both sides.
  · change (app (var d) (var b)) =α (app (var d) (var b))
    exact AlphaEquiv.refl _

-- The other four relations follow from Crole's theorems ...
example : AlphaEquivPFresh M N := (alphaEquiv_iff_alphaEquivPFresh M N).mp M_alphaEquiv_N
example : AlphaEquivP1 M N := (alphaEquiv_iff_alphaEquivP1 M N).mp M_alphaEquiv_N
example : AlphaEquivR M N := (alphaEquiv_iff_alphaEquivR M N).mp M_alphaEquiv_N
example : AlphaEquivRFresh M N := (alphaEquiv_iff_alphaEquivRFresh M N).mp M_alphaEquiv_N

-- ... and can also be derived with each relation's own rule. `pi#` swaps instead of renaming;
-- its witness only has to be fresh, and `d` is.
example : AlphaEquivPFresh M N := by
  apply AlphaEquivPFresh.abs (y := d)
  · simp only [fv]
    decide
  · change AlphaEquivPFresh (app (var d) (var b)) (app (var d) (var b))
    exact .app .var .var

-- `pi1` only asks that the witness does not occur in the two bodies.
example : AlphaEquivP1 M N := by
  apply AlphaEquivP1.abs (y := d)
  · simp only [vars]
    decide
  · change AlphaEquivP1 (app (var d) (var b)) (app (var d) (var b))
    exact .app .var .var

-- The body after renaming the bound `a` to `c`: `(a b)[a := c] = c b`.
theorem subst_body : (app (var a) (var b))[a := var c] = app (var c) (var b) := by
  change (app (var a) (var b)).subst a (var c) = _
  rw [subst, subst, subst, ite_eq_left rfl, ite_eq_right (by decide : b ≠ a)]

-- The renaming relations take one step: the axiom `α` renames the binder `a` to `c`, which does
-- not occur in `M` ...
example : AlphaEquivR M N := by
  have h : AlphaEquivR M (abs c ((app (var a) (var b))[a := var c])) :=
    AlphaEquivR.alpha (by simp only [vars]; decide)
  rwa [subst_body] at h

-- ... and `α#`, which only asks that `c` is fresh.
example : AlphaEquivRFresh M N := by
  have h : AlphaEquivRFresh M (abs c ((app (var a) (var b))[a := var c])) :=
    AlphaEquivRFresh.alpha (by simp only [fv]; decide)
  rwa [subst_body] at h

-- Proposition 4.3, side condition only `z ∉ {a, b}`: `λa. a z ∼²p λb. b a` with witness `z` ...
example : AlphaEquivP2 (abs a (app (var a) (var z))) (abs b (app (var b) (var a))) := by
  apply AlphaEquivP2.abs (z := z)
  · decide
  -- Swapping `z` with the binders turns both bodies into `z a`: the free `z` on the left has
  -- become the bound atom, and the free `a` on the right a free `a`.
  · change AlphaEquivP2 (app (var z) (var a)) (app (var z) (var a))
    exact .app .var .var

-- ... but the two terms are not α-equivalent: α-equivalent terms have the same free atoms.
example : ¬ ((abs a (app (var a) (var z))) =α (abs b (app (var b) (var a)))) := by
  intro h
  have hfv := h.same_fv
  have hl : (abs a (app (var a) (var z))).fv = {z} := by decide
  have hr : (abs b (app (var b) (var a))).fv = {a} := by decide
  rw [hl, hr] at hfv
  exact absurd hfv (by decide)

-- With no side condition at all: `λa. b a ∼³p λb. a b`, with witness `b` ...
example : AlphaEquivP3 (abs a (app (var b) (var a))) (abs b (app (var a) (var b))) := by
  apply AlphaEquivP3.abs (z := b)
  -- Swapping `b` with `a` on the left and doing nothing on the right gives `a b` twice.
  change AlphaEquivP3 (app (var a) (var b)) (app (var a) (var b))
  exact .app .var .var

-- ... but again the free atoms differ, `{b}` against `{a}`.
example : ¬ ((abs a (app (var b) (var a))) =α (abs b (app (var a) (var b)))) := by
  intro h
  have hfv := h.same_fv
  have hl : (abs a (app (var b) (var a))).fv = {b} := by decide
  have hr : (abs b (app (var a) (var b))).fv = {a} := by decide
  rw [hl, hr] at hfv
  exact absurd hfv (by decide)

-- Lemma 6.3: a swap with an unused atom is substitution up to `∼r`. In `a (λa. a)` the swap
-- `(z a)` also replaces the bound `a`, giving `z (λz. z)` ...
example : (app (var a) (abs a (var a))).swap z a = app (var z) (abs z (var z)) := by
  rw [swap, permute, permute, permute, permute, Equiv.swap_apply_right]

-- ... while `[a := z]` replaces only the free `a`, giving `z (λa. a)` ...
example : (app (var a) (abs a (var a)))[a := var z] = app (var z) (abs a (var a)) := by
  change (app (var a) (abs a (var a))).subst a (var z) = _
  rw [subst, subst, subst, ite_eq_left rfl, ite_eq_left rfl]

-- ... and the two results differ only in the name of a bound atom.
example : AlphaEquivR ((app (var a) (abs a (var a))).swap z a)
    ((app (var a) (abs a (var a)))[a := var z]) :=
  alphaEquivR_swap_subst_var (by simp only [vars]; decide)

-- The β-redex `(λa. a b) c` and its contractum `c b`, for the de Bruijn part below.
abbrev redex : Term Atom := app M (var c)
abbrev contractum : Term Atom := app (var c) (var b)

end Named

section DeBruijn

open Cslib.LambdaCalculus.Unscoped.Untyped Cslib.LambdaCalculus.Unscoped.Untyped.Term
open Cslib.LambdaCalculus.NamedDeBruijn
open Cslib.LambdaCalculus.Named.Untyped (TermAlpha BetaAlpha churchRosser_betaAlpha)
open scoped Cslib.LambdaCalculus.Named.Untyped.TermAlpha

-- `f` (`fromTerm`) sends `M = λa. a b` to `λ. 0 2`: the bound atom becomes index 0, the free `b`
-- (atom 1) becomes index 2, one more because it sits under one binder.
theorem fromTerm_M : fromTerm M = abs (app (var 0) (var 2)) := by
  -- `f` follows the term: atoms become indices, the binder becomes `dLAM`.
  rw [fromTerm_abs, fromTerm_app, fromTerm_var, fromTerm_var]
  change dLAM 0 (app (var 0) (var 1)) = _
  -- `dLAM i t` lifts every index of `t` past the new binder ...
  rw [Term.dLAM, lift_app, lift_var, lift_var, ite_eq_right (by decide : ¬ 0 < 0),
    ite_eq_right (by decide : ¬ 1 < 0)]
  -- ... and then replaces the lifted `i`, here `1`, by the bound index `0`.
  rw [dsub_app, dsub_var, dsub_var, ite_eq_left rfl, ite_eq_right (by decide : 2 ≠ 1)]

-- `N = λc. c b` has the same image; this computation is the same as for `M`, so it is left to
-- `decide`.
theorem fromTerm_N : fromTerm N = abs (app (var 0) (var 2)) := by decide

-- In general, `f (λx. x y) = λ. 0 (ŷ + 1)` for distinct atoms `x` and `y`.
example (x y : Atom) (h : x ≠ y) :
    fromTerm (.abs x (.app (.var x) (.var y))) = abs (app (var 0) (var (y.val + 1))) := by
  simpa [fromTerm_abs, fromTerm_app, fromTerm_var, Term.dLAM, Term.dsub_var, Term.dsub_app,
    Term.lift_var, Term.lift_app] using
    fun e => h (Atom.ext e.symm)

-- `λb. b a` is a different term.
example : fromTerm (.abs b (.app (.var b) (.var a))) = abs (app (var 0) (var 1)) := by decide

-- Equal images give α-equivalence (Theorem 11, injectivity of `f`).
example : M =α N := fromTerm_alphaEquiv_iff.mp (fromTerm_M.trans fromTerm_N.symm)

-- On the quotient `Λα`, `f` is the bijection `dbEquiv`; on a class it is `f` of a representative.
example : dbEquiv ⟦M⟧α = abs (app (var 0) (var 2)) := fromTerm_M

-- A β-step on the named side: `(λa. a b) c →β c b` in `Λα`.
theorem named_beta_step : BetaAlpha ⟦redex⟧α ⟦contractum⟧α := by
  -- The rule contracts the redex to the substitution `(a b)[a := c]` ...
  have h := BetaAlpha.red a ⟦.app (.var a) (.var b)⟧α ⟦.var c⟧α
  -- ... where application, abstraction and substitution on classes are computed on
  -- representatives ...
  rw [TermAlpha.abs_mk, TermAlpha.app_mk, TermAlpha.subst_mk] at h
  -- ... and the substitution gives `c b`.
  rwa [subst_body] at h

-- The corresponding `→d` step on de Bruijn terms, `(λ. 0 2) 2 →d 2 1`, by Theorem 20.
example : Beta (app (abs (app (var 0) (var 2))) (var 2)) (app (var 2) (var 1)) :=
  betaAlpha_iff_beta.mp named_beta_step

-- Theorem 20 as a relation isomorphism, and Church-Rosser for `→β` on `Λα` transported along it.
noncomputable example : BetaAlpha (Var := Atom) ≃r Beta := dbRelIso
example : Relation.Confluent (BetaAlpha (Var := Atom)) := churchRosser_betaAlpha

-- `dLAM` is not injective: `λa. a` and `λc. c` give the same de Bruijn term `λ. 0`.
example : dLAM 0 (var 0) = abs (var 0) := by decide
example : dLAM 2 (var 2) = abs (var 0) := by decide

-- Definition 8: under a binder the swap `(a b)` acts through `inc`, which exchanges the indices
-- `1` and `2`. So `λ. 1`, read `λx. a`, becomes `λ. 2`, read `λx. b` ...
example : FinPerm.swap a b • abs (var 1) = abs (var 2) := by decide

-- ... whereas swapping the indices `0` and `1` inside the binder would give `λ. 0`, the identity.
example : abs (FinPerm.swap a b • var 1) = abs (var 0) := by decide

end DeBruijn

end CslibTests.AlphaEquivalence
