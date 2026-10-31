/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.FromTerm
public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.LiftingPermutation

/-! # `→d` and `→d'` coincide, and the isomorphism `dB ≅ λNα` (paper, Section 4.3)

The second half of Section 4.3 of [Norrish2007a], for β-reduction.

## Main statements

* `Term.dbeta'_of_beta` : **Lemma 16**, `→d ⊆ →d'` (HOL `dbeta_dbeta'`).
* `Term.dpm_nsub` : **Lemma 17**, `nsub` under a permutation; the index `i` is not permuted
  (HOL `dpm_nsub`).
* `Term.Beta.equivariant` : `→d` is equivariant, by rule induction using Lemma 17.
* `Term.beta_of_dbeta'` : **Lemma 18**, `→d' ⊆ →d` (HOL `dbeta'_dbeta`).
* `Term.dbeta'_iff_beta` : **Theorem 19**, `t →d' u ⇔ t →d u` (HOL `dbeta_dbeta'_eqn`).
* `NamedDeBruijn.betaAlpha_iff_beta`, `NamedDeBruijn.isomorphism` : **Theorem 20**: `dB` with
  `→d` and `λNα` with `→β` are isomorphic, as witnessed by `f` (HOL `dbeta_ccbeta_eqn`).
* `NamedDeBruijn.dbRelIso` : Theorem 20 as a Mathlib relation isomorphism.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do
  Work*][Norrish2007a]
* [Tobias Nipkow, *More Church-Rosser proofs (in Isabelle/HOL)*][Nipkow2001]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.Unscoped.Untyped

open Cslib.Logic.Nominal

namespace Term

/-- **Lemma 16** (HOL `dbeta_dbeta'`): `→d ⊆ →d'`.  The `abs` case is Theorem 15. -/
lemma dbeta'_of_beta {t u : Term} (h : t ⭢β u) : t →d' u := by
  induction h with
  | red t' s => exact dbeta'_dABS_redex t' s
  | appL _ ih => exact DBeta'.appL _ ih
  | appR _ ih => exact DBeta'.appR _ ih
  | abs _ ih =>
      exact (dABS_rules_are_dLAM_compatible DBeta'
        DBeta'.equivariant).mpr (fun i _ _ h => DBeta'.lam i h) _ _ ih

/-- **Lemma 17** (HOL `dpm_nsub`): `π · (nsub t i u) = nsub (π · t) i (inc i (π) · u)`. -/
lemma dpm_nsub (π : FinPerm) (t : Term) (i : ℕ) (u : Term) :
    π • (nsub t i u) = nsub (π • t) i ((incPerm i π) • u) := by
  induction u generalizing π t i with
  | var m =>
      rw [dpm_var, incPerm_apply]
      simp only [nsub_var, incFun, gincAtom, gdecAtom, Atom.ofNat]
      split_ifs <;> simp_all [dpm_var, Atom.ofNat] <;> split_ifs <;> grind
  | app u₁ u₂ ih₁ ih₂ => simp only [nsub_app, dpm_app, ih₁, ih₂]
  | abs u ih => simp only [nsub_abs, dpm_abs, ih, incPerm_zero_incPerm, lift_dpm]

/-- `→d` is equivariant, by rule induction using Lemma 17 (HOL `dbeta_dpm`). -/
lemma Beta.dpm {t u : Term} (h : t ⭢β u) (π : FinPerm) : (π • t) ⭢β (π • u) := by
  induction h generalizing π with
  | red t' s =>
      simp only [dpm_app, dpm_abs]
      rw [show t'.sub 0 s = nsub s 0 t' from rfl, dpm_nsub π s 0 t']
      exact Beta.red _ _
  | appL _ ih => simp only [dpm_app]; exact Beta.appL (ih π)
  | appR _ ih => simp only [dpm_app]; exact Beta.appR (ih π)
  | abs _ ih => simp only [dpm_abs]; exact Beta.abs (ih _)

/-- Equivariance of `→d` in if-and-only-if form, as required by Theorem 15. -/
lemma Beta.equivariant (π : FinPerm) (t u : Term) : (π • t) ⭢β (π • u) ↔ t ⭢β u := by
  refine ⟨fun h => ?_, fun h => Beta.dpm h π⟩
  have h2 := Beta.dpm h π⁻¹
  rwa [inv_smul_smul, inv_smul_smul] at h2

/-- **Lemma 18** (HOL `dbeta'_dbeta`): `→d' ⊆ →d`.  The `dLAM` case is Theorem 15 for `→d`. -/
lemma beta_of_dbeta' {t u : Term} (h : t →d' u) : t ⭢β u := by
  induction h with
  | red i t u => exact beta_dLAM_redex i t u
  | appL _ _ ih => exact Beta.appL ih
  | appR _ _ ih => exact Beta.appR ih
  | lam i _ ih =>
      exact (dABS_rules_are_dLAM_compatible Beta Beta.equivariant).mp
        (fun _ _ h => Beta.abs h) i _ _ ih

/-- **Theorem 19** (Relations `→d` and `→d'` Coincide, HOL `dbeta_dbeta'_eqn`). -/
theorem dbeta'_iff_beta {t u : Term} : t →d' u ↔ t ⭢β u :=
  ⟨beta_of_dbeta', dbeta'_of_beta⟩

end Term

end Cslib.LambdaCalculus.Unscoped.Untyped

namespace Cslib.LambdaCalculus.NamedDeBruijn

open Cslib.Logic.Nominal
open Cslib.LambdaCalculus.Unscoped.Untyped
open Cslib.LambdaCalculus.Named.Untyped (TermAlpha BetaAlpha)
open scoped Cslib.LambdaCalculus.Named.Untyped

/-- **Theorem 20**, homomorphism part: `M →β N ⇔ f M →d f N` (HOL `dbeta_ccbeta_eqn`). -/
theorem betaAlpha_iff_beta {M N : TermAlpha Atom} : M →βα N ↔ toDB M ⭢β toDB N := by
  rw [betaAlpha_iff_dbeta', Term.dbeta'_iff_beta]

/-- **Theorem 20**: `dB` with `→d` and `λNα` with `→β` are isomorphic in the sense of
equation (3). -/
theorem isomorphism :
    ∃ f : TermAlpha Atom ≃ Term, ∀ M N, M →βα N ↔ f M ⭢β f N :=
  ⟨dbEquiv, fun _ _ => betaAlpha_iff_beta⟩

/-- Theorem 20 as a Mathlib relation isomorphism between `→β` on `Λα` and `→d` on `dB`. -/
noncomputable def dbRelIso : BetaAlpha (Var := Atom) ≃r Beta :=
  ⟨dbEquiv, betaAlpha_iff_beta.symm⟩

end Cslib.LambdaCalculus.NamedDeBruijn
