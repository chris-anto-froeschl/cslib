/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.FromTerm
public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.LiftingPermutation

/-! # Named and de Bruijn β-reduction are isomorphic

Nipkow's β-reduction `→d` on de Bruijn terms [Nipkow2001] coincides with `→d'`, so `f` is an
isomorphism between β-reduction on `Λα` and `→d` [Norrish2007a].

## Main statements

* `Term.dbeta'_iff_beta` : `t →d' u ⇔ t →d u`.
* `NamedDeBruijn.isomorphism`, `NamedDeBruijn.dbRelIso` : `Λα` with `→β` and de Bruijn terms with
  `→d` are isomorphic via `f`.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do
  Work*][Norrish2007a]
* [Tobias Nipkow, *More Church-Rosser proofs (in Isabelle/HOL)*][Nipkow2001]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.Unscoped.Untyped

open Cslib.Logic.Nominal

namespace Term

/-- Lemma 16 [Norrish2007a]: `→d ⊆ →d'`. The `abs` case is `dABS_rules_are_dLAM_compatible`. -/
lemma dbeta'_of_beta {t u : Term} (h : t ⭢β u) : t →d' u := by
  induction h with
  | red t' s => exact dbeta'_dABS_redex t' s
  | appL _ ih => exact DBeta'.appL _ ih
  | appR _ ih => exact DBeta'.appR _ ih
  | abs _ ih =>
      exact (dABS_rules_are_dLAM_compatible DBeta'
        DBeta'.equivariant).mpr (fun i _ _ h => DBeta'.lam i h) _ _ ih

/-- Lemma 17 [Norrish2007a]: `π · (nsub t i u) = nsub (π · t) i (inc i (π) · u)`. -/
lemma dpm_nsub (π : FinPerm) (t : Term) (i : ℕ) (u : Term) :
    π • (nsub t i u) = nsub (π • t) i ((incPerm i π) • u) := by
  induction u generalizing π t i with
  | var m =>
      rw [dpm_var, incPerm_apply]
      simp only [nsub_var, incFun, gincAtom, gdecAtom, Atom.ofNat]
      split_ifs <;> simp_all [dpm_var, Atom.ofNat] <;> split_ifs <;> grind
  | app u₁ u₂ ih₁ ih₂ => simp only [nsub_app, dpm_app, ih₁, ih₂]
  | abs u ih => simp only [nsub_abs, dpm_abs, ih, incPerm_zero_incPerm, lift_dpm]

/-- `→d` is equivariant, by rule induction using `dpm_nsub`. -/
lemma Beta.dpm {t u : Term} (h : t ⭢β u) (π : FinPerm) : (π • t) ⭢β (π • u) := by
  induction h generalizing π with
  | red t' s =>
      simp only [dpm_app, dpm_abs]
      rw [show t'.sub 0 s = nsub s 0 t' from rfl, dpm_nsub π s 0 t']
      exact Beta.red _ _
  | appL _ ih => simp only [dpm_app]; exact Beta.appL (ih π)
  | appR _ ih => simp only [dpm_app]; exact Beta.appR (ih π)
  | abs _ ih => simp only [dpm_abs]; exact Beta.abs (ih _)

/-- Equivariance of `→d` in if-and-only-if form, as required by
`dABS_rules_are_dLAM_compatible`. -/
lemma Beta.equivariant (π : FinPerm) (t u : Term) : (π • t) ⭢β (π • u) ↔ t ⭢β u := by
  refine ⟨fun h => ?_, fun h => Beta.dpm h π⟩
  have h2 := Beta.dpm h π⁻¹
  rwa [inv_smul_smul, inv_smul_smul] at h2

/-- Lemma 18 [Norrish2007a]: `→d' ⊆ →d`. The `dLAM` case is
`dABS_rules_are_dLAM_compatible` for `→d`. -/
lemma beta_of_dbeta' {t u : Term} (h : t →d' u) : t ⭢β u := by
  induction h with
  | red i t u => exact beta_dLAM_redex i t u
  | appL _ _ ih => exact Beta.appL ih
  | appR _ _ ih => exact Beta.appR ih
  | lam i _ ih =>
      exact (dABS_rules_are_dLAM_compatible Beta Beta.equivariant).mp
        (fun _ _ h => Beta.abs h) i _ _ ih

/-- Theorem 19 [Norrish2007a]: `→d` and `→d'` coincide. -/
theorem dbeta'_iff_beta {t u : Term} : t →d' u ↔ t ⭢β u :=
  ⟨beta_of_dbeta', dbeta'_of_beta⟩

end Term

end Cslib.LambdaCalculus.Unscoped.Untyped

namespace Cslib.LambdaCalculus.NamedDeBruijn

open Cslib.Logic.Nominal
open Cslib.LambdaCalculus.Unscoped.Untyped
open Cslib.LambdaCalculus.Named.Untyped (TermAlpha BetaAlpha)
open scoped Cslib.LambdaCalculus.Named.Untyped

/-- `f` preserves and reflects β-reduction: `M →β N ⇔ f M →d f N`. -/
theorem betaAlpha_iff_beta {M N : TermAlpha Atom} : M →βα N ↔ toDB M ⭢β toDB N := by
  rw [betaAlpha_iff_dbeta', Term.dbeta'_iff_beta]

/-- Theorem 20 [Norrish2007a]: `Λα` with `→β` and de Bruijn terms with `→d` are isomorphic. -/
theorem isomorphism :
    ∃ f : TermAlpha Atom ≃ Term, ∀ M N, M →βα N ↔ f M ⭢β f N :=
  ⟨dbEquiv, fun _ _ => betaAlpha_iff_beta⟩

/-- `isomorphism` as a Mathlib relation isomorphism between `→β` on `Λα` and `→d`. -/
noncomputable def dbRelIso : BetaAlpha (Var := Atom) ≃r Beta :=
  ⟨dbEquiv, betaAlpha_iff_beta.symm⟩

end Cslib.LambdaCalculus.NamedDeBruijn
