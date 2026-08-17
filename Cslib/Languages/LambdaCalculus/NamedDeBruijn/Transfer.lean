/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.Eta
public import Cslib.Languages.LambdaCalculus.Unscoped.Untyped.ChurchRosser
public import Batteries.Util.ProofWanted

/-! # Using the isomorphism: transporting results from `dB` to `Λα` (paper, Sections 1 and 5)

This file is the pay-off of the formalisation of

* Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*,
  TPHOLs 2007.

The point of the paper (Section 1, and the conclusion of Section 5) is not the isomorphism
`dB ≅ λNα` (**Theorem 20**, `NamedDeBruijn.isomorphism`) for its own sake, but the fact that it
lets one *transport* results: a theorem proved on de Bruijn terms — where reasoning is
first-order and machine-friendly — becomes a theorem about the α-quotiented named calculus
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

The section *Milestones still open* at the end of this file states, as `proof_wanted`
declarations, the results that this development stops short of.  `proof_wanted` elaborates and
type-checks a statement without recording a proof and without introducing a `sorry`, so these
are honest "wanted" statements rather than assumed facts.  The library theory each of them
needs is spelled out there and in `NamedDeBruijn-roadmap.md`.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*][NV2007]
-/

@[expose] public section

open Relation

namespace Cslib.LambdaCalculus.NamedDeBruijn

/-! ### Abstract transport along an isomorphism of reduction systems

Equation (3) of the paper defines an isomorphism of reduction systems to be a bijection `f`
with `M → N ⇔ f M → f N`.  The following two lemmas are all there is to "results transfer along
an isomorphism"; they are stated for arbitrary types and relations. -/

section Transport

variable {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}

/-- A bijection intertwining two relations intertwines their reflexive-transitive closures. -/
theorem Relation.reflTransGen_equiv_iff (e : α ≃ β) (h : ∀ a b, r a b ↔ s (e a) (e b))
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

/-- Confluence transports along an isomorphism of reduction systems (paper, equation (3)):
this is the sense in which "de Bruijn terms really do work". -/
theorem Equiv.confluent_of_equiv (e : α ≃ β) (h : ∀ a b, r a b ↔ s (e a) (e b))
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
theorem Equiv.normal_iff_of_equiv (e : α ≃ β) (h : ∀ a b, r a b ↔ s (e a) (e b)) (a : α) :
    Normal r a ↔ Normal s (e a) := by
  constructor
  · rintro hn ⟨b, hb⟩
    exact hn ⟨e.symm b, (h _ _).mpr (by rwa [e.apply_symm_apply])⟩
  · rintro hn ⟨b, hb⟩
    exact hn ⟨e b, (h _ _).mp hb⟩

end Transport

open CatCrypt.Nominal
open Cslib.LambdaCalculus.Unscoped.Untyped
open Cslib.LambdaCalculus.Named.Untyped (TermAlpha BetaAlpha EtaAlpha)
open scoped Cslib.LambdaCalculus.Named.Untyped.TermAlpha

/-! ### The uniqueness half of the characterisation (5) of `f`

The paper obtains `f` from Pitts' α-structural recursion principle, which delivers a *unique*
function satisfying the equations (5).  Existence is `toDB`; the uniqueness statement is
elementary once `f` is in hand, and is recorded here because it is what makes the equations (5)
a *definition* of `f` rather than three properties of one particular map. -/

/-- **Uniqueness in (5)**: `f` is the only map `Λα → dB` satisfying the paper's equations. -/
theorem toDB_unique (g : TermAlpha Atom → Term)
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

/-! ### Multi-step reduction and Church–Rosser for `λNα` -/

/-- The multi-step form of **Theorem 20**: `M ↠β N` in `λNα` iff `f M ↠d f N` in `dB`. -/
theorem reflTransGen_betaAlpha_iff {M N : TermAlpha Atom} :
    ReflTransGen BetaAlpha M N ↔ ReflTransGen Beta (toDB M) (toDB N) :=
  Relation.reflTransGen_equiv_iff dbEquiv (fun _ _ => betaAlpha_iff_beta) M N

/-- **The Church–Rosser theorem for `λNα`**, obtained from `churchRosser_beta` on de Bruijn
terms purely by transport along the isomorphism `f` of **Theorem 20**.

This is the paper's thesis in a single line: a confluence proof carried out on de Bruijn terms
is a confluence proof for the named, α-quotiented calculus. -/
theorem churchRosser_betaAlpha : Confluent (BetaAlpha (Var := Atom)) :=
  Equiv.confluent_of_equiv dbEquiv (fun _ _ => betaAlpha_iff_beta) churchRosser_beta

/-- β-normal forms correspond along `f`. -/
theorem normal_betaAlpha_iff {M : TermAlpha Atom} :
    Normal BetaAlpha M ↔ Normal Beta (toDB M) :=
  Equiv.normal_iff_of_equiv dbEquiv (fun _ _ => betaAlpha_iff_beta) M

/-- The multi-step form of the η-part of Section 4.4. -/
theorem reflTransGen_etaAlpha_iff {M N : TermAlpha Atom} :
    ReflTransGen EtaAlpha M N ↔ ReflTransGen NEta (toDB M) (toDB N) :=
  Relation.reflTransGen_equiv_iff dbEquiv (fun _ _ => etaAlpha_iff_neta) M N

/-- η-normal forms correspond along `f`. -/
theorem normal_etaAlpha_iff {M : TermAlpha Atom} :
    Normal EtaAlpha M ↔ Normal NEta (toDB M) :=
  Equiv.normal_iff_of_equiv dbEquiv (fun _ _ => etaAlpha_iff_neta) M

/-! ## Milestones still open

The declarations below are `proof_wanted`s: statements that elaborate but carry no proof.  They
are the natural next steps, and each is annotated with the theory that is currently missing.

### (a) α-structural induction for `Λα` (Pitts; paper, Sections 2.1 and 4.2)

The paper's proofs on the named side use Pitts' α-structural recursion and induction, in the
"BVC-compatible" form: when proving a property of all `M : Λα` one may assume that the bound
variable of an abstraction avoids any fixed finite set of names.  Cslib has no such principle,
neither for the raw named syntax nor for the quotient.  With the isomorphism in hand the
*induction* principle can be derived on the de Bruijn side, by induction on `Term.dbsize` of the
image, which is precisely the paper's message; that derivation is `TermAlpha.bvc_induction`
below, so the induction half of this milestone is now available.

The recursion principle proper (a unique `h : Λα → X` from equations plus a freshness condition
on binders, for `X` a nominal set) is not stated here: it would first need `Λα` to be equipped
with a `FinPerm`-action and shown to be a nominal set with `supp M = fv M`, which Cslib does not
provide either (see `NamedDeBruijn-roadmap.md`, item 2). -/

/-- **α-structural (BVC) induction for `Λα`** — the induction half of milestone (a), and one
more instance of the paper's thesis: to prove a property of every α-equivalence class it
suffices to treat abstractions whose bound name avoids a fixed finite set `C` of names.

The proof is by complete induction on `dbsize (f M)`, the size of the de Bruijn image, which is
well defined on the quotient precisely because `f` is (Theorem 11); the renaming step is the
named counterpart `Term.abs_swap_alphaEquiv` of `Term.dLAM_eq_dLAM_iff`.  So the induction
principle that Pitts' theory would supply is here *derived* from the de Bruijn side. -/
theorem TermAlpha.bvc_induction {motive : TermAlpha Atom → Prop} (C : Finset Atom)
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

/-! ### (b) Confluence of η and of βη on `Λα`

`Equiv.confluent_of_equiv` reduces each of these to the corresponding statement on de Bruijn
terms, and `reflTransGen_etaAlpha_iff` already transports the multi-step relation.  What is
missing is on the `dB` side: `Cslib.LambdaCalculus.Unscoped.Untyped` proves Church–Rosser for β
only (`ChurchRosser.lean`), with no development for `NEta` or for `Beta ∪ NEta`.  Cslib *does*
have both results for its locally nameless calculus (`LocallyNameless/Untyped/
FullEtaConfluence.lean`, `FullBetaEtaConfluence.lean`), so an alternative route is item (d). -/

/-- **Milestone (b1)**: confluence of Nipkow-style η-reduction on de Bruijn terms; missing from
Cslib's unscoped calculus. -/
proof_wanted Unscoped.Untyped.churchRosser_neta : Confluent NEta

/-- **Milestone (b2)**: confluence of η-reduction on `λNα`; immediate from (b1) by
`Equiv.confluent_of_equiv dbEquiv (fun _ _ => etaAlpha_iff_neta)`. -/
proof_wanted churchRosser_etaAlpha : Confluent (EtaAlpha (Var := Atom))

/-- **Milestone (b3)**: confluence of βη on `λNα`.  Needs confluence of `fun t u => Beta t u ∨
NEta t u` on `dB`, which in turn needs the commutation of β and η (Hindley–Rosen). -/
proof_wanted churchRosser_betaEtaAlpha :
    Confluent (fun M N : TermAlpha Atom => BetaAlpha M N ∨ EtaAlpha M N)

/-! ### (c) The λ-calculus consequences of confluence, on `Λα`

Once `churchRosser_betaAlpha` is available the usual corollaries are pure rewriting theory and
`Cslib.Foundations.Relation.Confluence` already has the generic lemmas; the statement below is
the one a λ-calculus text would quote; it is recorded here as the first such corollary. -/

/-- β-normal forms in `λNα` are unique — the standard corollary of `churchRosser_betaAlpha`,
and hence, transitively, of the de Bruijn Church–Rosser theorem. -/
theorem TermAlpha.normal_form_unique {M N₁ N₂ : TermAlpha Atom}
    (h₁ : ReflTransGen BetaAlpha M N₁) (h₂ : ReflTransGen BetaAlpha M N₂)
    (hn₁ : Normal BetaAlpha N₁) (hn₂ : Normal BetaAlpha N₂) : N₁ = N₂ := by
  obtain ⟨w, hw₁, hw₂⟩ := churchRosser_betaAlpha h₁ h₂
  rw [hn₁.reflTransGen_eq hw₁, hn₂.reflTransGen_eq hw₂]

/-! ### (d) Connecting the third representation in Cslib: locally nameless

Cslib's most developed λ-calculus is the locally nameless one, which carries confluence for β,
η and βη, standardisation, leftmost reduction and strong normalisation results.  None of that
is available for `dB` or for `Λα`.  Extending the paper's methodology, a bijection between
`Λα` (equivalently `dB`) and the *locally closed* locally nameless terms, homomorphic for the
respective reductions, would transport all of it in one step.  This needs: a predicate carving
out the locally closed terms, the translation in both directions, and the analogue of
Theorem 12 for it.  It is a development of the same size as the present one, and is the largest
single missing item; see `NamedDeBruijn-roadmap.md`, item 5. -/

end Cslib.LambdaCalculus.NamedDeBruijn
