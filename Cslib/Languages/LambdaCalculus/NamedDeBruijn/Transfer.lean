/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.Isomorphism
public import Cslib.Languages.LambdaCalculus.Unscoped.Untyped.ChurchRosser

/-! # Using the isomorphism: transporting results from `dB` to `Λα`

An isomorphism of reduction systems (Theorem 20, `NamedDeBruijn.isomorphism`) transports every
property stated in terms of the relation.
Here it turns the Church–Rosser theorem for `→d` on `dB` (`Unscoped.Untyped.churchRosser_beta`) into
the Church–Rosser theorem for `→β` on `Λα`.

## Main statements

* `churchRosser_betaAlpha` : the Church–Rosser theorem for `λNα`, transported along `f`.
* `TermAlpha.normal_form_unique` : uniqueness of β-normal forms in `Λα`.
-/

@[expose] public section

open Relation

namespace Cslib.LambdaCalculus.NamedDeBruijn

open Cslib.Logic.Nominal
open Cslib.LambdaCalculus.Unscoped.Untyped
open Cslib.LambdaCalculus.Named.Untyped (TermAlpha BetaAlpha)

/-- Confluence transports backwards along an isomorphism of reduction systems (paper,
equation (3)): push both reduction paths forwards, join them, and pull the join back. -/
private lemma confluent_of_relIso {X Y : Type*} {r : X → X → Prop} {s : Y → Y → Prop}
    (e : r ≃r s) (hs : Confluent s) : Confluent r := by
  have back {x y : Y} (h : ReflTransGen s x y) : ReflTransGen r (e.symm x) (e.symm y) :=
    h.lift e.symm fun _ _ => e.symm.map_rel_iff.mpr
  intro x y z hxy hxz
  obtain ⟨w, hyw, hzw⟩ :=
    hs (hxy.lift e fun _ _ => e.map_rel_iff.mpr) (hxz.lift e fun _ _ => e.map_rel_iff.mpr)
  exact ⟨e.symm w, by simpa using back hyw, by simpa using back hzw⟩

/-- The Church–Rosser theorem for `λNα`, transported from `churchRosser_beta` on de Bruijn terms
along `f` (Theorem 20). -/
lemma churchRosser_betaAlpha : Confluent (BetaAlpha (Var := Atom)) :=
  confluent_of_relIso dbRelIso churchRosser_beta

/-- β-normal forms in `λNα` are unique. -/
lemma TermAlpha.normal_form_unique {M N₁ N₂ : TermAlpha Atom}
    (h₁ : ReflTransGen BetaAlpha M N₁) (h₂ : ReflTransGen BetaAlpha M N₂)
    (hn₁ : Normal BetaAlpha N₁) (hn₂ : Normal BetaAlpha N₂) : N₁ = N₂ := by
  obtain ⟨w, hw₁, hw₂⟩ := churchRosser_betaAlpha h₁ h₂
  rw [hn₁.reflTransGen_eq hw₁, hn₂.reflTransGen_eq hw₂]

end Cslib.LambdaCalculus.NamedDeBruijn
