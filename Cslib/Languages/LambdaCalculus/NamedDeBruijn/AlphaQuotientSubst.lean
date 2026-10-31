/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.FromTerm

/-! # Substitution on `Λα` is the substitution of `λNα`

`TermAlpha.subst` lifts raw substitution to the quotient, while [Norrish2006] defines it on the
quotient by recursion. Both give the same function, so `BetaAlpha` is the β-reduction of `λNα`.

## Main statements

* `TermAlpha.bvc_induction` : induction on `Λα` with the bound name avoiding a finite set.
* `TermAlpha.subst_unique` : substitution is the only map satisfying the equations (6) of
  [Norrish2006].

## References

* [Michael Norrish, *Mechanising λ-calculus using a classical first order theory of terms with
  permutations*][Norrish2006]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.NamedDeBruijn

open Cslib.Logic.Nominal
open Cslib.LambdaCalculus.Unscoped.Untyped
open Cslib.LambdaCalculus.Named.Untyped (TermAlpha)
open scoped Cslib.LambdaCalculus.Named.Untyped Cslib.LambdaCalculus.Named.Untyped.TermAlpha

/-- α-structural (BVC) induction for `Λα`: to prove a property of every `M`, it suffices to
treat abstractions whose bound name avoids a fixed finite set `C`. Derived from the de Bruijn
side, by complete induction on `dbsize (f M)`. -/
lemma TermAlpha.bvc_induction {motive : TermAlpha Atom → Prop} (C : Finset Atom)
    (var : ∀ x : Atom, motive (TermAlpha.var x))
    (app : ∀ M N, motive M → motive N → motive (TermAlpha.app M N))
    (abs : ∀ (x : Atom) (M), x ∉ C → motive M → motive (TermAlpha.abs x M)) :
    ∀ M, motive M := by
  have key : ∀ n (M : TermAlpha Atom), Term.dbsize (toDB M) < n → motive M := by
    intro n
    induction n with
    | zero => intro M h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro M hM
      induction M using TermAlpha.ind with
      | _ m =>
        match m with
        | .var x => exact var x
        | .app m₁ m₂ =>
            rw [← TermAlpha.app_mk] at hM ⊢
            rw [toDB_app, Term.dbsize_app] at hM
            exact app _ _ (ih _ (by omega)) (ih _ (by omega))
        | .abs x m₀ =>
            obtain ⟨y, hy⟩ := HasFresh.fresh_exists (C ∪ m₀.fv)
            simp only [Finset.mem_union, not_or] at hy
            have halpha : (Named.Untyped.Term.abs x m₀) =α
                (Named.Untyped.Term.abs y (m₀.swap y x)) :=
              Named.Untyped.Term.abs_swap_alphaEquiv hy.2
            have heq : (⟦Named.Untyped.Term.abs x m₀⟧α : TermAlpha Atom)
                = TermAlpha.abs y ⟦m₀.swap y x⟧α := TermAlpha.mk_eq_mk.mpr halpha
            have hsize : Term.dbsize (toDB (⟦Named.Untyped.Term.abs x m₀⟧α))
                = Term.dbsize (toDB ⟦m₀.swap y x⟧α) + 1 := by
              rw [heq, toDB_abs, Term.dbsize_dLAM]
            rw [hsize] at hM
            rw [heq]
            exact abs y _ hy.1 (ih _ (by omega))
  exact fun M => key (Term.dbsize (toDB M) + 1) M (Nat.lt_succ_self _)

/-- Substitution on `Λα` is the only map satisfying the equations (6) of [Norrish2006] for
`M ↦ M[v := N]`. -/
lemma TermAlpha.subst_unique (v : Atom) (n : Named.Untyped.Term Atom)
    (g : TermAlpha Atom → TermAlpha Atom)
    (hvar : g (TermAlpha.var v) = ⟦n⟧α)
    (hvar' : ∀ u, u ≠ v → g (TermAlpha.var u) = TermAlpha.var u)
    (happ : ∀ M N, g (TermAlpha.app M N) = TermAlpha.app (g M) (g N))
    (habs : ∀ u M, u ≠ v → u ∉ n.fv → g (TermAlpha.abs u M) = TermAlpha.abs u (g M)) :
    g = fun M => TermAlpha.subst M v ⟦n⟧α := by
  funext M
  refine TermAlpha.bvc_induction (motive := fun M => g M = TermAlpha.subst M v ⟦n⟧α)
    ({v} ∪ n.fv) ?_ ?_ ?_ M
  · intro u
    change _ = TermAlpha.subst ⟦Named.Untyped.Term.var u⟧α v ⟦n⟧α
    rw [TermAlpha.subst_mk]
    obtain rfl | huv := eq_or_ne u v
    · rw [hvar]
      simp [Named.Untyped.Term.subst]
    · rw [hvar' u huv]
      simp [Named.Untyped.Term.subst, huv, TermAlpha.var]
  · intro M N ihM ihN
    rw [happ, ihM, ihN]
    induction M using TermAlpha.ind with | _ m =>
    induction N using TermAlpha.ind with | _ k =>
    rw [TermAlpha.app_mk, TermAlpha.subst_mk, TermAlpha.subst_mk, TermAlpha.subst_mk,
      TermAlpha.app_mk]
    simp [Named.Untyped.Term.subst]
  · intro u M hu ih
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hu
    rw [habs u M hu.1 hu.2, ih]
    induction M using TermAlpha.ind with | _ m =>
    rw [TermAlpha.subst_mk, TermAlpha.abs_mk, TermAlpha.abs_mk, TermAlpha.subst_mk]
    simp [Named.Untyped.Term.subst, hu.1, hu.2]

end Cslib.LambdaCalculus.NamedDeBruijn
