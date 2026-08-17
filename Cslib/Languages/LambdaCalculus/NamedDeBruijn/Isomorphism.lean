/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.FromTerm
public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.LiftingPermutation

/-! # `→d` and `→d'` coincide, and the isomorphism `dB ≅ λNα` (paper, Sections 4.3 and 4.4)

This file completes the formalisation of

* Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*,
  TPHOLs 2007

for β-reduction: Section 4.3 (*The Homomorphism between `dB` and `dB'`*), culminating in
**Theorem 19** (`→d` and `→d'` are the same relation) and **Theorem 20** (the isomorphism
between `dB` and `λNα`).

## Main statements

* `Term.dbeta'_of_beta` : **Lemma 16**, `→d ⊆ →d'`.
* `Term.dpm_nsub` : **Lemma 17**, the "rather incomprehensible" behaviour of `nsub` under a
  permutation — note the odd way in which the permutation `π` does not affect the index `i`.
* `Term.Beta.equivariant` : `→d` is equivariant, by rule induction using **Lemma 17**.
* `Term.beta_of_dbeta'` : **Lemma 18**, `→d' ⊆ →d`.
* `Term.dbeta'_iff_beta` : **Theorem 19**, `t →d' u ⇔ t →d u`.
* `NamedDeBruijn.betaAlpha_iff_beta`, `NamedDeBruijn.isomorphism` : **Theorem 20**,
  the types `dB` and `λNα`, with their respective reduction relations `→d` and `→β`, are
  isomorphic, as witnessed by the bijection `f`.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*][NV2007]
* [Tobias Nipkow, *More Church-Rosser proofs (in Isabelle/HOL)*][Nipkow2001]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.Unscoped.Untyped

open CatCrypt.Nominal

namespace Term

/-! ### Lemma 16 — `→d ⊆ →d'` -/

/-- **Lemma 16** (`→d ⊆ →d'`).  A rule induction over the definition of `→d`: the redex case is
handled by **Lemma 13**, the `dAPP` congruence cases are immediate, and the `dABS` congruence
case follows from **Lemma 14** and **Theorem 10** via **Theorem 15**. -/
theorem dbeta'_of_beta {t u : Term} (h : Beta t u) : DBeta' t u := by
  induction h with
  | red t' s => exact dbeta'_dABS_redex t' s
  | appL _ ih => exact DBeta'.appL _ ih
  | appR _ ih => exact DBeta'.appR _ ih
  | abs _ ih =>
      exact (dABS_rules_are_dLAM_compatible DBeta'
        (fun π _ _ => DBeta'.equivariant π)).mpr (fun i _ _ h => DBeta'.lam i h) _ _ ih

/-! ### Lemma 17 and the equivariance of `→d` -/

/-- **Lemma 17** (HOL `dpm_nsub`): `π · (nsub t i u) = nsub (π · t) i (inc i (π) · u)`.
By structural induction on `u`; the `dV` case requires a number of splits on the ordering
possibilities between the index of the variable and `i`, and the `dABS` case uses **Lemma 9**. -/
theorem dpm_nsub (π : FinPerm) (t : Term) (i : ℕ) (u : Term) :
    π • (nsub t i u) = nsub (π • t) i ((incPerm i π) • u) := by
  induction u generalizing π t i with
  | var m =>
      rcases eq_or_ne m i with rfl | hmi
      · have h : incFun m π (Atom.ofNat m) = Atom.ofNat m := by
          simp [incFun, Atom.ofNat]
        simp only [nsub_var, Nat.lt_irrefl, ite_false, ite_true, dpm_var, incPerm_apply, h]
        simp
      · set d : ℕ := if m < i then m else m - 1 with hd
        have hdec : gdecAtom i (Atom.ofNat m) = Atom.ofNat d := by
          rcases lt_or_gt_of_ne hmi with h | h
          · simp [gdecAtom, Atom.ofNat, hd, h, h.le]
          · have : ¬ (m ≤ i) := by omega
            simp [gdecAtom, Atom.ofNat, hd, this, show ¬ (m < i) by omega]
        set w : ℕ := (π (Atom.ofNat d)).val with hw
        have hval : (incFun i π (Atom.ofNat m)).val = if w < i then w else w + 1 := by
          have hne : (Atom.ofNat m).val ≠ i := by simpa [Atom.ofNat] using hmi
          simp only [incFun, hne, ite_false, hdec, gincAtom, ← hw]
          split_ifs <;> rfl
        rw [dpm_var, incPerm_apply, hval]
        have hrhs : nsub (π • t) i (var (if w < i then w else w + 1)) = var w := by
          by_cases h : w < i
          · simp only [h, ite_true, nsub_var]
            rw [ite_eq_right (by omega : ¬ i < w), ite_eq_right (by omega : ¬ w = i)]
          · simp only [h, ite_false, nsub_var]
            rw [ite_eq_left (by omega : i < w + 1)]
            congr 1
        rw [hrhs]
        rcases lt_or_gt_of_ne hmi with h | h
        · simp only [nsub_var, ite_eq_right (by omega : ¬ i < m), ite_eq_right hmi, dpm_var, hw,
            hd, ite_eq_left h]
        · simp only [nsub_var, ite_eq_left (show i < m by omega), dpm_var, hw, hd,
            ite_eq_right (by omega : ¬ m < i)]
  | app u₁ u₂ ih₁ ih₂ => simp only [nsub_app, dpm_app, ih₁, ih₂]
  | abs u ih => simp only [nsub_abs, dpm_abs, ih, incPerm_zero_incPerm, lift_dpm]

/-- `→d` is equivariant, by rule induction using **Lemma 17** (HOL `dbeta_dpm`). -/
theorem Beta.dpm {t u : Term} (h : Beta t u) (π : FinPerm) : Beta (π • t) (π • u) := by
  induction h generalizing π with
  | red t' s =>
      simp only [dpm_app, dpm_abs]
      rw [show t'.sub 0 s = nsub s 0 t' from rfl, dpm_nsub π s 0 t']
      exact Beta.red _ _
  | appL _ ih => simp only [dpm_app]; exact Beta.appL (ih π)
  | appR _ ih => simp only [dpm_app]; exact Beta.appR (ih π)
  | abs _ ih => simp only [dpm_abs]; exact Beta.abs (ih _)

/-- Equivariance of `→d` in if-and-only-if form, as required by **Theorem 15**. -/
theorem Beta.equivariant (π : FinPerm) (t u : Term) : Beta (π • t) (π • u) ↔ Beta t u := by
  refine ⟨fun h => ?_, fun h => Beta.dpm h π⟩
  have h2 := Beta.dpm h π⁻¹
  rwa [inv_smul_smul, inv_smul_smul] at h2

/-! ### Lemma 18 and Theorem 19 -/

/-- **Lemma 18** (`→d' ⊆ →d`).  The redex case is `beta_dLAM_redex`, the application
congruences are immediate, and the abstraction congruence follows from **Theorem 15** applied to
the equivariant relation `→d`. -/
theorem beta_of_dbeta' {t u : Term} (h : DBeta' t u) : Beta t u := by
  induction h with
  | red i t u => exact beta_dLAM_redex i t u
  | appL _ _ ih => exact Beta.appL ih
  | appR _ _ ih => exact Beta.appR ih
  | lam i _ ih =>
      exact (dABS_rules_are_dLAM_compatible Beta Beta.equivariant).mp
        (fun _ _ h => Beta.abs h) i _ _ ih

/-- **Theorem 19** (Relations `→d` and `→d'` Coincide). -/
theorem dbeta'_iff_beta {t u : Term} : DBeta' t u ↔ Beta t u :=
  ⟨beta_of_dbeta', dbeta'_of_beta⟩

end Term

end Cslib.LambdaCalculus.Unscoped.Untyped

namespace Cslib.LambdaCalculus.NamedDeBruijn

open CatCrypt.Nominal
open Cslib.LambdaCalculus.Unscoped.Untyped
open Cslib.LambdaCalculus.Named.Untyped (TermAlpha BetaAlpha)

/-- **Theorem 20**, homomorphism part: `M →β N ⇔ f M →d f N`.  Immediate from **Theorem 12** and
**Theorem 19**. -/
theorem betaAlpha_iff_beta {M N : TermAlpha Atom} :
    BetaAlpha M N ↔ Beta (toDB M) (toDB N) := by
  rw [betaAlpha_iff_dbeta', Term.dbeta'_iff_beta]

/-- **Theorem 20** (Isomorphism): the types `dB` and `λNα`, with their respective reduction
relations `→d` and `→β`, are isomorphic, as witnessed by the bijective `f`.

This is the statement of isomorphism from equation (3) of the paper: a bijection that is
homomorphic for the two reduction relations. -/
theorem isomorphism :
    ∃ f : TermAlpha Atom ≃ Term, ∀ M N, BetaAlpha M N ↔ Beta (f M) (f N) :=
  ⟨dbEquiv, fun _ _ => betaAlpha_iff_beta⟩

end Cslib.LambdaCalculus.NamedDeBruijn
