/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.Isomorphism

/-! # Bonus: η-reduction (paper, Section 4.4)

The final section of

* Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*,
  TPHOLs 2007

repeats the development of Section 4.3 for η-reduction.  Thanks to **Theorem 15** (which was
stated for an arbitrary equivariant relation) only the redex rules and the equivariance of the
two relations have to be considered.

## Main definitions

* `Term.NEta` : Nipkow's η-reduction `→ne`; its redex rule
  `0 ∉ dFV t → dABS (dAPP t (dV 0)) →ne nsub u 0 t` uses `nsub` only to decrement the free
  indices of `t` as it moves out from underneath the abstraction, so the choice of `u` is
  immaterial.
* `Term.DEta` : the "traditional style" η-reduction `→e`, whose redex rule is
  `i ∉ dFV t → dLAM i (dAPP t (dV i)) →e t`.

## Main statements

* `Term.nsub_lift`, `Term.lift_nsub` : the two Nipkow-style lemmas quoted in Section 4.4.
* `Term.deta_iff_neta` : `→e` and `→ne` coincide.
* `NamedDeBruijn.etaAlpha_iff_deta` : η-reduction on `Λα` corresponds to `→e`, hence
  (with the previous result) to Nipkow's `→ne`; the η-analogue of **Theorem 20**.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*][NV2007]
* [Tobias Nipkow, *More Church-Rosser proofs (in Isabelle/HOL)*][Nipkow2001]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.Unscoped.Untyped

open CatCrypt.Nominal

/-- Nipkow's η-reduction `→ne` (paper, Section 4.4).  In the redex rule the choice of `u` is
immaterial, see `Term.nsub_indep_of_not_mem_dFV`. -/
inductive NEta : Term → Term → Prop where
  /-- Contraction of an η-redex, decrementing the free indices of `t`. -/
  | red {t : Term} (u : Term) : 0 ∉ t.dFV → NEta (Term.abs (Term.app t (Term.var 0)))
      (Term.nsub u 0 t)
  /-- Congruence in the left argument of an application. -/
  | appL {t t' : Term} (u : Term) : NEta t t' → NEta (Term.app t u) (Term.app t' u)
  /-- Congruence in the right argument of an application. -/
  | appR {u u' : Term} (t : Term) : NEta u u' → NEta (Term.app t u) (Term.app t u')
  /-- Congruence under a `dABS`-abstraction. -/
  | abs {t t' : Term} : NEta t t' → NEta (Term.abs t) (Term.abs t')

/-- The "traditional style" η-reduction `→e` on de Bruijn terms, using `dLAM` (paper,
Section 4.4). -/
inductive DEta : Term → Term → Prop where
  /-- Contraction of an η-redex `dLAM i (dAPP t (dV i))` with `i` not free in `t`. -/
  | red {t : Term} (i : ℕ) : i ∉ t.dFV → DEta (Term.dLAM i (Term.app t (Term.var i))) t
  /-- Congruence in the left argument of an application. -/
  | appL {t t' : Term} (u : Term) : DEta t t' → DEta (Term.app t u) (Term.app t' u)
  /-- Congruence in the right argument of an application. -/
  | appR {u u' : Term} (t : Term) : DEta u u' → DEta (Term.app t u) (Term.app t u')
  /-- Congruence under a `dLAM`-abstraction. -/
  | lam {t t' : Term} (i : ℕ) : DEta t t' → DEta (Term.dLAM i t) (Term.dLAM i t')

namespace Term

/-- HOL `nsub_lift`, one of the lemmas stated by Nipkow: `nsub u n (lift t n) = t`. -/
@[simp] theorem nsub_lift (t u : Term) (n : ℕ) : nsub u n (lift t n) = t := by
  induction t generalizing u n with
  | var i =>
      simp only [lift_var]; split_ifs <;> simp only [nsub_var] <;> split_ifs <;>
        first | rfl | (congr 1; omega)
  | app t u iht ihu => simp only [lift_app, nsub_app, iht, ihu]
  | abs t ih => simp only [lift_abs, nsub_abs, ih]

/-- The similar result stated and proved in the paper: `n ∉ dFV t → lift (nsub u n t) n = t`
(HOL `lift_nsub`). -/
theorem lift_nsub {t : Term} {n : ℕ} (u : Term) (h : n ∉ dFV t) : lift (nsub u n t) n = t := by
  induction t generalizing u n with
  | var m =>
      simp only [mem_dFV_var] at h
      simp only [nsub_var]
      split_ifs <;> simp only [lift_var] <;> split_ifs <;> first | rfl | (congr 1; omega)
  | app t u iht ihu =>
      simp only [mem_dFV_app, not_or] at h
      simp only [nsub_app, lift_app, iht _ h.1, ihu _ h.2]
  | abs t ih =>
      simp only [mem_dFV_abs] at h
      simp only [nsub_abs, lift_abs, ih _ h]

/-- HOL `nipkow_eta_lemma`: if `i` is not free in `t`, then `nsub _ i t` does not depend on the
term being substituted — it merely decrements the free indices of `t`. -/
theorem nsub_indep_of_not_mem_dFV {t : Term} {i : ℕ} (h : i ∉ dFV t) (u v : Term) :
    nsub u i t = nsub v i t := by
  induction t generalizing u v i with
  | var m =>
      simp only [mem_dFV_var] at h
      simp only [nsub_var]
      split_ifs <;> rfl
  | app t₁ t₂ iht₁ iht₂ =>
      simp only [mem_dFV_app, not_or] at h
      simp only [nsub_app]
      rw [iht₁ h.1 u v, iht₂ h.2 u v]
  | abs t ih =>
      simp only [mem_dFV_abs] at h
      simp only [nsub_abs]
      rw [ih h (lift u 0) (lift v 0)]

/-- `→ne` is preserved by permutations (HOL `neta_dpm`); the proof uses **Lemma 17**. -/
theorem _root_.Cslib.LambdaCalculus.Unscoped.Untyped.NEta.dpm {t u : Term} (h : NEta t u)
    (π : FinPerm) : NEta (π • t) (π • u) := by
  induction h generalizing π with
  | @red t v h0 =>
      have hz : incFun 0 π (Atom.ofNat 0) = Atom.ofNat 0 := by simp [incFun, Atom.ofNat]
      have hfree : (0 : ℕ) ∉ dFV ((incPerm 0 π) • t) := by
        rw [mem_dFV_dpm]
        rintro ⟨j, hj, hval⟩
        rw [incPerm_apply, incFun_zero_val] at hval
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · exact h0 hj
        · rw [ite_eq_right (by omega : ¬ j = 0)] at hval
          omega
      simp only [dpm_abs, dpm_app, dpm_var, hz, incPerm_apply]
      rw [dpm_nsub π v 0 t]
      exact NEta.red _ hfree
  | appL _ _ ih => simp only [dpm_app]; exact NEta.appL _ (ih π)
  | appR _ _ ih => simp only [dpm_app]; exact NEta.appR _ (ih π)
  | abs _ ih => simp only [dpm_abs]; exact NEta.abs (ih _)

/-- `→ne` is equivariant (HOL `neta_dpm`); the proof uses **Lemma 17**. -/
theorem _root_.Cslib.LambdaCalculus.Unscoped.Untyped.NEta.equivariant (π : FinPerm) (t u : Term) :
    NEta (π • t) (π • u) ↔ NEta t u := by
  refine ⟨fun h => ?_, fun h => h.dpm π⟩
  have h2 := h.dpm π⁻¹
  rwa [inv_smul_smul, inv_smul_smul] at h2

/-- `→e` is preserved by permutations (HOL `eta_dpm`); the proof uses **Theorem 10**. -/
theorem _root_.Cslib.LambdaCalculus.Unscoped.Untyped.DEta.dpm {t u : Term} (h : DEta t u)
    (π : FinPerm) : DEta (π • t) (π • u) := by
  induction h generalizing π with
  | @red t i h0 =>
      have hfree : (π (Atom.ofNat i)).val ∉ dFV (π • t) := by
        rw [mem_dFV_dpm]
        rintro ⟨j, hj, hval⟩
        have hji : Atom.ofNat j = Atom.ofNat i := π.val.injective (Atom.ext hval)
        exact h0 (by rwa [show j = i from congrArg Atom.val hji] at hj)
      rw [dpm_dLAM, dpm_app, dpm_var]
      exact DEta.red _ hfree
  | appL _ _ ih => simp only [dpm_app]; exact DEta.appL _ (ih π)
  | appR _ _ ih => simp only [dpm_app]; exact DEta.appR _ (ih π)
  | lam i _ ih => rw [dpm_dLAM, dpm_dLAM]; exact DEta.lam _ (ih _)

/-- `→e` is equivariant (HOL `eta_dpm_eqn`); the proof uses **Theorem 10**. -/
theorem _root_.Cslib.LambdaCalculus.Unscoped.Untyped.DEta.equivariant (π : FinPerm) (t u : Term) :
    DEta (π • t) (π • u) ↔ DEta t u := by
  refine ⟨fun h => ?_, fun h => h.dpm π⟩
  have h2 := h.dpm π⁻¹
  rwa [inv_smul_smul, inv_smul_smul] at h2

/-- The `→ne`-redexes reduce under `→e` (HOL `alt_neta_redex`). -/
theorem deta_nABS_redex {t : Term} (u : Term) (h : 0 ∉ dFV t) :
    DEta (abs (app t (var 0))) (nsub u 0 t) := by
  set t' := nsub u 0 t with ht'
  obtain ⟨i, hi⟩ := dfresh_exists t'
  have hlift : lift t' 0 = t := lift_nsub u h
  have key : dLAM i (app t' (var i)) = abs (app t (var 0)) := by
    have h1 : i + 1 ∉ dFV (lift t' 0) := by
      simp only [mem_dFV_lift]
      rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · omega
      · simp only [Nat.add_sub_cancel] at h2
        exact hi h2
    simp only [dLAM, lift_app, dsub_app, lift_var, Nat.not_lt_zero, ite_false, dsub_var]
    rw [dsub_of_not_mem_dFV h1, hlift]
    simp
  rw [← key]
  exact DEta.red i hi

/-- The `→e`-redexes reduce under `→ne` (HOL `alt_eta_redex`). -/
theorem neta_dLAM_redex {t : Term} {i : ℕ} (h : i ∉ dFV t) :
    NEta (dLAM i (app t (var i))) t := by
  have h1 : i + 1 ∉ dFV (lift t 0) := by
    simp only [mem_dFV_lift]
    rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · omega
    · simp only [Nat.add_sub_cancel] at h2
      exact h h2
  have key : dLAM i (app t (var i)) = abs (app (lift t 0) (var 0)) := by
    simp only [dLAM, lift_app, dsub_app, lift_var, Nat.not_lt_zero, ite_false, dsub_var]
    rw [dsub_of_not_mem_dFV h1]
    simp
  have h0 : (0 : ℕ) ∉ dFV (lift t 0) := by
    simp only [mem_dFV_lift]
    rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> omega
  rw [key]
  have hred := NEta.red (t := lift t 0) t h0
  rwa [nsub_lift] at hred

/-- `→e ⊆ →ne` (HOL `eta_neta`).  The congruence case is **Theorem 15**. -/
theorem neta_of_deta {t u : Term} (h : DEta t u) : NEta t u := by
  induction h with
  | red i h0 => exact neta_dLAM_redex h0
  | appL _ _ ih => exact NEta.appL _ ih
  | appR _ _ ih => exact NEta.appR _ ih
  | lam i _ ih =>
      exact (dABS_rules_are_dLAM_compatible NEta NEta.equivariant).mp
        (fun _ _ h => NEta.abs h) i _ _ ih

/-- `→ne ⊆ →e` (HOL `neta_eta`).  The congruence case is **Theorem 15**. -/
theorem deta_of_neta {t u : Term} (h : NEta t u) : DEta t u := by
  induction h with
  | red u h0 => exact deta_nABS_redex u h0
  | appL _ _ ih => exact DEta.appL _ ih
  | appR _ _ ih => exact DEta.appR _ ih
  | abs _ ih =>
      exact (dABS_rules_are_dLAM_compatible DEta DEta.equivariant).mpr
        (fun i _ _ h => DEta.lam i h) _ _ ih

/-- The η-analogue of **Theorem 19** (HOL `neta_eq_eta`): `→e` and `→ne` coincide. -/
theorem deta_iff_neta {t u : Term} : DEta t u ↔ NEta t u :=
  ⟨neta_of_deta, deta_of_neta⟩

end Term

end Cslib.LambdaCalculus.Unscoped.Untyped

namespace Cslib.LambdaCalculus.NamedDeBruijn

open CatCrypt.Nominal
open Cslib.LambdaCalculus.Unscoped.Untyped
open Cslib.LambdaCalculus.Named.Untyped (TermAlpha EtaAlpha)
open scoped Cslib.LambdaCalculus.Named.Untyped.TermAlpha

/-- The "→" half of the η-analogue of Theorem 12: a rule induction on `→ηα`.  The side
condition of the redex rule transfers along `mem_dFV_fromTerm`. -/
theorem deta_of_etaAlpha {M N : TermAlpha Atom} (h : EtaAlpha M N) :
    DEta (toDB M) (toDB N) := by
  induction h with
  | red x m hx =>
      have hdfv : x.val ∉ Term.dFV (fromTerm m) := fun hc => hx (by
        have h := (mem_dFV_fromTerm m x.val).mp hc
        rwa [Atom.val_ofNat] at h)
      simpa using DEta.red (t := fromTerm m) x.val hdfv
  | appL Z _ ih => simpa using DEta.appL (toDB Z) ih
  | appR Z _ ih => simpa using DEta.appR (toDB Z) ih
  | abs x _ ih => simpa using DEta.lam x.val ih

/-- The "←" half of the η-analogue of Theorem 12: a rule induction on `→e`, generalised over
the preimages of the two de Bruijn terms, using the inversion lemmas for `f`. -/
theorem etaAlpha_of_deta : ∀ {t u : Term}, DEta t u →
    ∀ M N : TermAlpha Atom, toDB M = t → toDB N = u → EtaAlpha M N := by
  intro t u h
  induction h with
  | @red t i hi =>
      intro M N hM hN
      obtain ⟨M₀, rfl, h₀⟩ := toDB_eq_dLAM hM
      obtain ⟨M₁, M₂, rfl, h₁, h₂⟩ := toDB_eq_app h₀
      obtain ⟨m, rfl⟩ := Quotient.exists_rep M₁
      have hN' : N = TermAlpha.mk m := toDB_injective (by rw [hN]; exact h₁.symm)
      have hM₂ : M₂ = TermAlpha.var (Atom.ofNat i) := toDB_injective (by rw [h₂]; rfl)
      subst hN'
      rw [hM₂]
      refine EtaAlpha.red _ m ?_
      intro hc
      exact hi (h₁ ▸ (mem_dFV_fromTerm m i).mpr hc)
  | appL z _ ih =>
      intro M N hM hN
      obtain ⟨M₁, M₂, rfl, h₁, h₂⟩ := toDB_eq_app hM
      obtain ⟨N₁, N₂, rfl, k₁, k₂⟩ := toDB_eq_app hN
      rw [show M₂ = N₂ from toDB_injective (by rw [h₂, k₂])]
      exact EtaAlpha.appL _ (ih M₁ N₁ h₁ k₁)
  | appR z _ ih =>
      intro M N hM hN
      obtain ⟨M₁, M₂, rfl, h₁, h₂⟩ := toDB_eq_app hM
      obtain ⟨N₁, N₂, rfl, k₁, k₂⟩ := toDB_eq_app hN
      rw [show M₁ = N₁ from toDB_injective (by rw [h₁, k₁])]
      exact EtaAlpha.appR _ (ih M₂ N₂ h₂ k₂)
  | lam i _ ih =>
      intro M N hM hN
      obtain ⟨M₀, rfl, h₀⟩ := toDB_eq_dLAM hM
      obtain ⟨N₀, rfl, k₀⟩ := toDB_eq_dLAM hN
      exact EtaAlpha.abs _ (ih M₀ N₀ h₀ k₀)

/-- η-reduction on `Λα` corresponds to `→e` on `dB` (HOL `eta_eq_lam_eta`). -/
theorem etaAlpha_iff_deta {M N : TermAlpha Atom} :
    EtaAlpha M N ↔ DEta (toDB M) (toDB N) :=
  ⟨deta_of_etaAlpha, fun h => etaAlpha_of_deta h M N rfl rfl⟩

/-- The η-analogue of **Theorem 20**: the bijection `f` is a homomorphism for η-reduction as
well, so `dB` with Nipkow's `→ne` is isomorphic to `λNα` with η-reduction. -/
theorem etaAlpha_iff_neta {M N : TermAlpha Atom} :
    EtaAlpha M N ↔ NEta (toDB M) (toDB N) := by
  rw [etaAlpha_iff_deta, Term.deta_iff_neta]

end Cslib.LambdaCalculus.NamedDeBruijn
