/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.Eta
public import Cslib.Languages.LambdaCalculus.Unscoped.Untyped.ChurchRosser
public import Batteries.Util.ProofWanted

/-! # Using the isomorphism: transporting results from `dB` to `Λα`

This file is the pay-off of the formalisation of

* Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*,
  TPHOLs 2007.

The point of the paper (Section 1, and the conclusion of Section 5) is not the isomorphism
`dB ≅ λNα` (**Theorem 20**, `NamedDeBruijn.isomorphism`) for its own sake, but the fact that it
lets one *transport* results: a theorem proved on de Bruijn terms (where reasoning is
first-order and machine-friendly) becomes a theorem about the α-quotiented named calculus
`Λα`, whose statements are the ones a λ-calculus paper actually makes.

Here that programme is carried out for the first non-trivial example available in Cslib, the
Church–Rosser theorem: `Cslib.LambdaCalculus.Unscoped.Untyped.churchRosser_beta` proves
confluence of `→d` on `dB` by parallel reduction and complete developments, and the isomorphism
turns it into confluence of `→β` on `Λα`, with no further λ-calculus reasoning.

## Main statements

* `Relation.reflTransGen_equiv_iff`, `Equiv.confluent_of_equiv` : the abstract content of
  "isomorphism of reduction systems" (paper, equation (3)): a bijection intertwining two
  relations intertwines their multi-step closures, and transports confluence.
* `reflTransGen_betaAlpha_iff` : the multi-step form of **Theorem 20**, `M ↠β N ⇔ f M ↠d f N`.
* `churchRosser_betaAlpha` : the Church–Rosser theorem for `λNα`, transported along `f`.
* `normal_betaAlpha_iff` : `M` is a `→β`-normal form of `Λα` iff `f M` is a `→d`-normal form
  of `dB`; similarly `normal_etaAlpha_iff` for η.
* `toDB_unique` : the uniqueness half of the characterisation (5) of `f`, i.e. `f` is the only
  function `Λα → dB` satisfying the paper's three equations.  (Existence is `toDB` together
  with `toDB_var`, `toDB_app`, `toDB_abs`.)
* `TermAlpha.bvc_induction` : α-structural ("bound variable convention") induction for `Λα`,
  derived from the de Bruijn side rather than from Pitts' nominal theory.
* `TermAlpha.normal_form_unique` : uniqueness of β-normal forms in `Λα`.

## Next milestones

The `proof_wanted` declarations at the end of this file state confluence of η and of βη on
`Λα`.  Both reduce, along the isomorphism, to results on `dB` that Cslib does not have yet.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do
  Work*][Norrish2007a]
-/

@[expose] public section

open Relation

namespace Cslib.LambdaCalculus.NamedDeBruijn

section Transport

variable {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}

/-- A bijection intertwining two relations intertwines their reflexive-transitive closures. -/
lemma Relation.reflTransGen_equiv_iff (e : α ≃ β) (h : ∀ a b, r a b ↔ s (e a) (e b))
    (a b : α) : ReflTransGen r a b ↔ ReflTransGen s (e a) (e b) := by
  constructor
  · intro hab
    induction hab with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.tail ((h _ _).mp hstep)
  · intro hab
    -- Induct on the `s`-derivation, transporting each element back along `e.symm`.
    have key : ∀ x y : β, ReflTransGen s x y → ∀ a : α, e a = x →
        ReflTransGen r a (e.symm y) := by
      intro x y hxy
      induction hxy with
      | refl => intro a ha; subst ha; simpa using ReflTransGen.refl
      | @tail y z _ hstep ih =>
          intro a ha
          refine (ih a ha).tail ?_
          refine (h _ _).mpr ?_
          rw [e.apply_symm_apply, e.apply_symm_apply]
          exact hstep
    simpa using key (e a) (e b) hab a rfl

/-- Confluence transports along an isomorphism of reduction systems (paper, equation (3)). -/
lemma Equiv.confluent_of_equiv (e : α ≃ β) (h : ∀ a b, r a b ↔ s (e a) (e b))
    (hs : Confluent s) : Confluent r := by
  intro x y z hxy hxz
  obtain ⟨w, hyw, hzw⟩ :=
    hs ((Relation.reflTransGen_equiv_iff e h x y).mp hxy)
      ((Relation.reflTransGen_equiv_iff e h x z).mp hxz)
  refine ⟨e.symm w, ?_, ?_⟩
  · exact (Relation.reflTransGen_equiv_iff e h y (e.symm w)).mpr
      (by rwa [e.apply_symm_apply])
  · exact (Relation.reflTransGen_equiv_iff e h z (e.symm w)).mpr
      (by rwa [e.apply_symm_apply])

/-- Normal forms correspond along an isomorphism of reduction systems. -/
lemma Equiv.normal_iff_of_equiv (e : α ≃ β) (h : ∀ a b, r a b ↔ s (e a) (e b)) (a : α) :
    Normal r a ↔ Normal s (e a) := by
  constructor
  · rintro hn ⟨b, hb⟩
    exact hn ⟨e.symm b, (h _ _).mpr (by rwa [e.apply_symm_apply])⟩
  · rintro hn ⟨b, hb⟩
    exact hn ⟨e b, (h _ _).mp hb⟩

end Transport

open Cslib.Logic.Nominal
open Cslib.LambdaCalculus.Unscoped.Untyped
open Cslib.LambdaCalculus.Named.Untyped (TermAlpha BetaAlpha EtaAlpha)
open scoped Cslib.LambdaCalculus.Named.Untyped.TermAlpha

/-- `f` is the only map `Λα → dB` satisfying the equations (5). -/
lemma toDB_unique (g : TermAlpha Atom → Term)
    (hvar : ∀ x : Atom, g (TermAlpha.var x) = Term.var x.val)
    (happ : ∀ M N, g (TermAlpha.app M N) = Term.app (g M) (g N))
    (habs : ∀ (x : Atom) (M), g (TermAlpha.abs x M) = Term.dLAM x.val (g M)) :
    g = toDB := by
  funext M
  induction M using TermAlpha.ind with
  | _ m =>
    induction m with
    | var x => exact hvar x
    | app m n ihm ihn =>
        have h : (⟦Named.Untyped.Term.app m n⟧α : TermAlpha Atom)
            = TermAlpha.app ⟦m⟧α ⟦n⟧α := rfl
        rw [h, happ, ihm, ihn, toDB_app]
    | abs x m ih =>
        have h : (⟦Named.Untyped.Term.abs x m⟧α : TermAlpha Atom)
            = TermAlpha.abs x ⟦m⟧α := rfl
        rw [h, habs, ih, toDB_abs]

/-- The multi-step form of Theorem 20: `M ↠β N` in `λNα` iff `f M ↠d f N` in `dB`. -/
lemma reflTransGen_betaAlpha_iff {M N : TermAlpha Atom} :
    ReflTransGen BetaAlpha M N ↔ ReflTransGen Beta (toDB M) (toDB N) :=
  Relation.reflTransGen_equiv_iff dbEquiv (fun _ _ => betaAlpha_iff_beta) M N

/-- The Church–Rosser theorem for `λNα`, transported from `churchRosser_beta` on de Bruijn terms
along `f` (Theorem 20). -/
lemma churchRosser_betaAlpha : Confluent (BetaAlpha (Var := Atom)) :=
  Equiv.confluent_of_equiv dbEquiv (fun _ _ => betaAlpha_iff_beta) churchRosser_beta

/-- β-normal forms correspond along `f`. -/
lemma normal_betaAlpha_iff {M : TermAlpha Atom} :
    Normal BetaAlpha M ↔ Normal Beta (toDB M) :=
  Equiv.normal_iff_of_equiv dbEquiv (fun _ _ => betaAlpha_iff_beta) M

/-- The multi-step form of the η-part of Section 4.4. -/
lemma reflTransGen_etaAlpha_iff {M N : TermAlpha Atom} :
    ReflTransGen EtaAlpha M N ↔ ReflTransGen NEta (toDB M) (toDB N) :=
  Relation.reflTransGen_equiv_iff dbEquiv (fun _ _ => etaAlpha_iff_neta) M N

/-- η-normal forms correspond along `f`. -/
lemma normal_etaAlpha_iff {M : TermAlpha Atom} :
    Normal EtaAlpha M ↔ Normal NEta (toDB M) :=
  Equiv.normal_iff_of_equiv dbEquiv (fun _ _ => etaAlpha_iff_neta) M

/-- α-structural (BVC) induction for `Λα`: to prove a property of every `M`, it suffices to
treat abstractions whose bound name avoids a fixed finite set `C`.  Derived from the de Bruijn
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
            have hsplit : toDB (⟦Named.Untyped.Term.app m₁ m₂⟧α)
                = Term.app (toDB ⟦m₁⟧α) (toDB ⟦m₂⟧α) := rfl
            rw [hsplit, Term.dbsize_app] at hM
            have h : (⟦Named.Untyped.Term.app m₁ m₂⟧α : TermAlpha Atom)
                = TermAlpha.app ⟦m₁⟧α ⟦m₂⟧α := rfl
            rw [h]
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

/-- Confluence of Nipkow's η-reduction on de Bruijn terms. -/
proof_wanted Unscoped.Untyped.churchRosser_neta : Confluent NEta

/-- Confluence of η-reduction on `λNα`; follows from `churchRosser_neta` by
`Equiv.confluent_of_equiv dbEquiv (fun _ _ => etaAlpha_iff_neta)`. -/
proof_wanted churchRosser_etaAlpha : Confluent (EtaAlpha (Var := Atom))

/-- Confluence of βη on `λNα`.  Needs confluence of `Beta ∪ NEta` on `dB`, for example by
Hindley-Rosen. -/
proof_wanted churchRosser_betaEtaAlpha :
    Confluent (fun M N : TermAlpha Atom => BetaAlpha M N ∨ EtaAlpha M N)

/-- β-normal forms in `λNα` are unique. -/
lemma TermAlpha.normal_form_unique {M N₁ N₂ : TermAlpha Atom}
    (h₁ : ReflTransGen BetaAlpha M N₁) (h₂ : ReflTransGen BetaAlpha M N₂)
    (hn₁ : Normal BetaAlpha N₁) (hn₂ : Normal BetaAlpha N₂) : N₁ = N₂ := by
  obtain ⟨w, hw₁, hw₂⟩ := churchRosser_betaAlpha h₁ h₂
  rw [hn₁.reflTransGen_eq hw₁, hn₂.reflTransGen_eq hw₂]

end Cslib.LambdaCalculus.NamedDeBruijn
