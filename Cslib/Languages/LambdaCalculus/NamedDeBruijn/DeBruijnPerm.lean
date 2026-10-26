/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.PureDeBruijn
public import Cslib.Logics.Nominal.Nominal

/-! # de Bruijn terms are a nominal set (paper, Sections 3 and 4.2)

This file formalises the paper's Section 3 (*Nominal Reasoning*) instantiated at the type of
pure de Bruijn terms, and the first part of Section 4.2 (*dB' vs λNα: Nominal Reasoning with
Indices*), up to and including **Theorem 10**.

## Main definitions

* `Term.gincAtom` : the guarded increment `ginc` of an atom (HOL `ginc_def`).
* `Term.incPerm` : `inc_g`, the increment of a permutation (**Definition 8**, generalised to an
  arbitrary guard as required for **Lemma 9**).
* `Term.dpm` : the permutation action on de Bruijn terms (**Definition 8**), packaged as the
  `MulAction FinPerm Term` instance, together with the `NomSet Term` instance whose support is
  the set of free indices.

## Main statements

* `Term.supports_dFV` : the free indices of a term support it (Section 4.2).
* `Term.lift_dpm` : **Lemma 9** (permutations and `lift`).
* `Term.dpm_dsub`, `Term.dpm_dLAM`, `DBeta'.equivariant` : **Theorem 10** (`sub` and `dLAM` have
  empty support; `→d'` is equivariant).

## Implementation notes

The paper represents a permutation as a list of pairs of strings (Definition 2), and therefore
has to state the third nominal axiom of (4) extensionally. Cslib's nominal library instead uses
`Cslib.Logic.Nominal.FinPerm`, the group of finitely supported bijections of `Atom`; the
extensionality axiom of (4) is then automatic, and the nominal-set axioms of (4) are exactly the
`MulAction FinPerm` laws.

Atoms are (wrapped) natural numbers, so the bijection between "strings" and numbers used
throughout Section 4 of the paper is `Atom.ofNat`/`Atom.val`:

| Paper  | Cslib          |
|--------|----------------|
| `î`    | `Atom.ofNat i` |
| `ŝ`    | `s.val`        |

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do
  Work*][Norrish2007a]
* [Andrew M. Pitts, *Alpha-structural recursion and induction*][Pitts2006]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.Unscoped.Untyped

open Cslib.Logic.Nominal

namespace Term

/-- `gincAtom g a` (HOL `ginc_def`): the guarded increment, `lift`'s shift on atoms. The atom
`a` is untouched if its index is below the guard `g`, and bumped by one otherwise. -/
def gincAtom (g : ℕ) (a : Atom) : Atom := if a.val < g then a else ⟨a.val + 1⟩

/-- The inverse of `gincAtom g` on its image (which is everything but the atom `ĝ`). -/
def gdecAtom (g : ℕ) (a : Atom) : Atom := if a.val ≤ g then a else ⟨a.val - 1⟩

/-- `gdecAtom g` undoes `gincAtom g`. -/
private lemma gdecAtom_gincAtom (g : ℕ) (a : Atom) : gdecAtom g (gincAtom g a) = a := by
  unfold gdecAtom gincAtom
  split_ifs <;> grind

/-- HOL `ginc_neq`: `ginc` never hits the guard. -/
lemma gincAtom_ne (g : ℕ) (a : Atom) : (gincAtom g a).val ≠ g := by
  grind [gincAtom]

/-- `gincAtom g` undoes `gdecAtom g` on every atom other than the guard. -/
private lemma gincAtom_gdecAtom {g : ℕ} {a : Atom} (h : a.val ≠ g) :
    gincAtom g (gdecAtom g a) = a := by
  obtain ⟨v⟩ := a
  unfold gdecAtom gincAtom
  split_ifs <;> grind

/-- The underlying function of `incPerm`: `π` transported along `gincAtom g`, and the identity at
the guard (compare HOL `lswapstr_inc_pm`). -/
def incFun (g : ℕ) (π : FinPerm) (a : Atom) : Atom :=
  if a.val = g then a else gincAtom g (π (gdecAtom g a))

/-- `incFun g π⁻¹` is a right inverse of `incFun g π`. -/
lemma incFun_incFun_inv (g : ℕ) (π : FinPerm) (a : Atom) :
    incFun g π (incFun g π⁻¹ a) = a := by
  by_cases h : a.val = g
  · simp [incFun, h]
  · simp only [incFun, h, ite_false, gincAtom_ne, gdecAtom_gincAtom, ← FinPerm.mul_apply,
      mul_inv_cancel, FinPerm.one_apply]
    exact gincAtom_gdecAtom h

/-- `incFun g π⁻¹` is a left inverse of `incFun g π`. -/
lemma incFun_inv_incFun (g : ℕ) (π : FinPerm) (a : Atom) :
    incFun g π⁻¹ (incFun g π a) = a := by
  simpa only [inv_inv] using incFun_incFun_inv g π⁻¹ a

/-- **Definition 8** [Norrish2007a], for an arbitrary guard `g`: the increment `inc g π` of a
permutation. It shifts the entries of `π` the way `lift t g` shifts indices: entries below `g`
stay, the others go up by one (HOL `inc_pm_def` applies `ginc g` to both atoms of every swap).
The resulting permutation fixes the gap `g`, which `gincAtom g` never hits (`gincAtom_ne`). The
paper's phrase "the index below which variables should not be touched" describes the entries,
not this action. `incPerm 0` is the paper's `inc`. -/
def incPerm (g : ℕ) (π : FinPerm) : FinPerm :=
  ⟨⟨incFun g π, incFun g π⁻¹, incFun_inv_incFun g π, incFun_incFun_inv g π⟩,
    (π.suppWitness.image (gincAtom g)) ∪ {⟨g⟩}, by
      intro a ha
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, not_or] at ha
      obtain ⟨himg, hg⟩ := ha
      have hne : a.val ≠ g := fun h => hg (by ext; exact h)
      have hnot : gdecAtom g a ∉ π.suppWitness := by
        intro hmem
        exact himg ⟨gdecAtom g a, hmem, gincAtom_gdecAtom hne⟩
      change incFun g π a = a
      rw [incFun, ite_eq_right hne, π.suppWitness_spec _ hnot, gincAtom_gdecAtom hne]⟩

/-- `incPerm g π` acts on atoms as `incFun g π`. -/
lemma incPerm_apply (g : ℕ) (π : FinPerm) (a : Atom) :
    incPerm g π a = incFun g π a :=
  rfl

/-- The action of an incremented permutation with guard `0`, in terms of indices. -/
lemma incFun_zero_val (π : FinPerm) (v : ℕ) :
    (incFun 0 π (Atom.ofNat v)).val =
      if v = 0 then 0 else (π (Atom.ofNat (v - 1))).val + 1 := by
  simp only [incFun, gincAtom, gdecAtom, Atom.ofNat, Nat.not_lt_zero, ite_false, Nat.le_zero_eq]
  split_ifs with h <;> first | exact h | rfl

/-- `lift` on a variable is the guarded increment of atoms. -/
private lemma lift_var_eq (i n : ℕ) : lift (var i) n = var (gincAtom n (Atom.ofNat i)).val := by
  grind [lift_var, gincAtom, Atom.ofNat]

/-- Incrementing the identity permutation gives the identity. -/
lemma incPerm_one (g : ℕ) : incPerm g 1 = 1 := by
  refine FinPerm.ext (fun a => ?_)
  simp only [incPerm_apply, incFun, FinPerm.one_apply]
  split_ifs with h
  · rfl
  · exact gincAtom_gdecAtom h

/-- Incrementing is multiplicative. -/
lemma incPerm_mul (g : ℕ) (π₁ π₂ : FinPerm) :
    incPerm g (π₁ * π₂) = incPerm g π₁ * incPerm g π₂ := by
  refine FinPerm.ext (fun a => ?_)
  simp only [incPerm_apply, incFun, FinPerm.mul_apply]
  by_cases h : a.val = g
  · simp [h]
  · simp only [h, ite_false, gincAtom_ne, gdecAtom_gincAtom]

/-- The `dABS` case of Lemma 9: `inc 0 (inc n π) = inc (n+1) (inc 0 π)`. -/
lemma incPerm_zero_incPerm (n : ℕ) (π : FinPerm) :
    incPerm 0 (incPerm n π) = incPerm (n + 1) (incPerm 0 π) := by
  refine FinPerm.ext (fun a => ?_)
  simp only [incPerm_apply, incFun, gincAtom, gdecAtom, Nat.not_lt_zero, ite_false,
    Nat.le_zero_eq]
  split_ifs <;> apply Atom.ext <;> (try dsimp only at *) <;> omega

/-- **Definition 8** [Norrish2007a]: the permutation action on `dB`. Under `dABS` the free
indices move up by one, so the permutation is incremented. -/
def dpm (π : FinPerm) : Term → Term
  | var i => var (π (Atom.ofNat i)).val
  | app t u => app (dpm π t) (dpm π u)
  | abs t => abs (dpm (incPerm 0 π) t)

/-- The identity permutation acts trivially (first condition of (4) [Norrish2007a]). -/
lemma dpm_one (t : Term) : dpm 1 t = t := by
  induction t with
  | var i => simp [dpm]
  | app t u iht ihu => simp [dpm, iht, ihu]
  | abs t ih => simp only [dpm, incPerm_one, ih]

/-- Acting by a product is acting twice (second condition of (4) [Norrish2007a]). -/
lemma dpm_mul (π₁ π₂ : FinPerm) (t : Term) : dpm (π₁ * π₂) t = dpm π₁ (dpm π₂ t) := by
  induction t generalizing π₁ π₂ with
  | var i => simp [dpm]
  | app t u iht ihu => simp [dpm, iht, ihu]
  | abs t ih => simp only [dpm, incPerm_mul, ih]

/-- de Bruijn terms carry a permutation action: the conditions (4) [Norrish2007a] hold. -/
instance : MulAction FinPerm Term where
  smul := dpm
  one_smul := dpm_one
  mul_smul := dpm_mul

/-- Definition 8 [Norrish2007a], `dV` case: `π · dV i = dV (π(î))`. -/
lemma dpm_var (π : FinPerm) (i : ℕ) : π • var i = var (π (Atom.ofNat i)).val := rfl

/-- Definition 8 [Norrish2007a], `dAPP` case. -/
lemma dpm_app (π : FinPerm) (t u : Term) : π • app t u = app (π • t) (π • u) := rfl

/-- Definition 8 [Norrish2007a], `dABS` case: under a binder the permutation is incremented. -/
lemma dpm_abs (π : FinPerm) (t : Term) : π • abs t = abs ((incPerm 0 π) • t) := rfl

/-- The free indices of a permuted term. -/
lemma mem_dFV_dpm (π : FinPerm) (t : Term) (i : ℕ) :
    i ∈ dFV (π • t) ↔ ∃ j ∈ dFV t, (π (Atom.ofNat j)).val = i := by
  induction t generalizing π i with
  | var m =>
      simp only [dpm_var, mem_dFV_var]
      constructor
      · rintro rfl; exact ⟨m, rfl, rfl⟩
      · rintro ⟨j, hj, rfl⟩; rw [hj]
  | app t u iht ihu =>
      simp only [dpm_app, mem_dFV_app, iht, ihu, or_and_right, exists_or]
  | abs t ih =>
      simp only [dpm_abs, mem_dFV_abs, ih]
      constructor
      · rintro ⟨j, hj, hv⟩
        rw [incPerm_apply, incFun_zero_val] at hv
        split_ifs at hv with h0
        exact ⟨j - 1, by rwa [Nat.sub_add_cancel (by omega)], by omega⟩
      · rintro ⟨j, hj, hv⟩
        refine ⟨j + 1, hj, ?_⟩
        rw [incPerm_apply, incFun_zero_val]
        simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, hv]

/-- The free indices of a de Bruijn term, as atoms, support it (Section 4.2 [Norrish2007a]; HOL
`dpm_fresh`). HOL's `dpm_supp` also shows that they are the least support; that is not needed
here. -/
lemma supports_dFV (t : Term) : Supports ((dFV t).image Atom.ofNat) t := by
  intro π hπ
  induction t generalizing π with
  | var i =>
      rw [dpm_var, hπ _ (by simp)]
      rfl
  | app t u iht ihu =>
      rw [dpm_app, iht π (fun a ha => hπ a ?_), ihu π (fun a ha => hπ a ?_)] <;>
        grind [mem_dFV_app]
  | abs t ih =>
      rw [dpm_abs]
      refine congrArg abs (ih (incPerm 0 π) (fun a ha => ?_))
      simp only [Finset.mem_image] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      apply Atom.ext
      rw [incPerm_apply, incFun_zero_val]
      split_ifs with h0
      · simp [Atom.ofNat, h0]
      · have hmem : Atom.ofNat (j - 1) ∈ (dFV (abs t)).image Atom.ofNat := by
          simp only [Finset.mem_image, mem_dFV_abs]
          exact ⟨j - 1, by rwa [show j - 1 + 1 = j by omega], rfl⟩
        rw [hπ _ hmem]
        simp only [Atom.ofNat]
        omega

/-- Permuting a term permutes its free indices (set form of HOL `IN_dFV_dpm`). Only used for
the `NomSet` instance below. -/
lemma dFV_dpm (t : Term) (π : FinPerm) :
    (dFV (π • t)).image Atom.ofNat = ((dFV t).image Atom.ofNat).image (π ·) := by
  ext a
  simp only [Finset.mem_image, mem_dFV_dpm]
  constructor
  · rintro ⟨i, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨Atom.ofNat j, ⟨j, hj, rfl⟩, Atom.val_ofNat _⟩
  · rintro ⟨b, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨(π (Atom.ofNat j)).val, ⟨j, hj, rfl⟩, Atom.val_ofNat _⟩

/-- de Bruijn terms form a nominal set, with support the set of free indices (Section 4.2
[Norrish2007a]). Not used by the current proofs, which define `f` on raw terms; kept for a future
definition of `f` by Pitts' recursion, which needs it. -/
instance : NomSet Term where
  toMulAction := inferInstance
  supp t := (dFV t).image Atom.ofNat
  supp_supports := supports_dFV
  supp_equivariant := dFV_dpm

/-- **Lemma 9** [Norrish2007a] (Permutations and `lift`):
`lift (π · t) n = (inc n π) · (lift t n)`. -/
lemma lift_dpm (π : FinPerm) (t : Term) (n : ℕ) :
    lift (π • t) n = (incPerm n π) • (lift t n) := by
  induction t generalizing π n with
  | var i =>
      rw [dpm_var, lift_var_eq, lift_var_eq, dpm_var]
      congr 1
      simp only [incPerm_apply, incFun, Atom.val_ofNat, gincAtom_ne, ite_false,
        gdecAtom_gincAtom]
  | app t u iht ihu => rw [dpm_app, lift_app, lift_app, dpm_app, iht, ihu]
  | abs t ih =>
      rw [dpm_abs, lift_abs, lift_abs, dpm_abs, ih, incPerm_zero_incPerm]

/-- **Theorem 10** [Norrish2007a], substitution part: `sub` has empty support,
`π · (sub t j u) = sub (π · t) (π(ĵ)) (π · u)` (HOL `dpm_sub`). -/
theorem dpm_dsub (π : FinPerm) (t : Term) (j : ℕ) (u : Term) :
    π • (dsub t j u) = dsub (π • t) (π (Atom.ofNat j)).val (π • u) := by
  induction u generalizing π t j with
  | var m =>
      simp only [dsub_var, dpm_var]
      obtain rfl | h := eq_or_ne m j
      · simp only [ite_true]
      · have h2 : (π (Atom.ofNat m)).val ≠ (π (Atom.ofNat j)).val := fun he =>
          h (congrArg Atom.val (π.val.injective (Atom.ext he)))
        simp only [h, h2, ite_false, dpm_var]
  | app u₁ u₂ ih₁ ih₂ => simp only [dsub_app, dpm_app, ih₁, ih₂]
  | abs u ih =>
      simp only [dsub_abs, dpm_abs, ih, ← lift_dpm]
      congr 1

/-- **Theorem 10** [Norrish2007a], abstraction part: `dLAM` has empty support,
`π · (dLAM i t) = dLAM (π(î)) (π · t)` (HOL `dpm_dLAM`). -/
theorem dpm_dLAM (π : FinPerm) (i : ℕ) (t : Term) :
    π • (dLAM i t) = dLAM (π (Atom.ofNat i)).val (π • t) := by
  simp only [dLAM, dpm_abs, dpm_dsub, dpm_var, ← lift_dpm]
  congr 1

end Term

/-- **Theorem 10** [Norrish2007a], forward direction of the equivariance of `→d'`, by rule
induction. -/
lemma DBeta'.dpm {t u : Term} (h : t →d' u) (π : FinPerm) : (π • t) →d' (π • u) := by
  induction h generalizing π with
  | red i t u =>
      rw [Term.dpm_app, Term.dpm_dLAM, Term.dpm_dsub]
      exact DBeta'.red _ _ _
  | appL z _ ih => rw [Term.dpm_app, Term.dpm_app]; exact DBeta'.appL _ (ih π)
  | appR z _ ih => rw [Term.dpm_app, Term.dpm_app]; exact DBeta'.appR _ (ih π)
  | lam i _ ih => rw [Term.dpm_dLAM, Term.dpm_dLAM]; exact DBeta'.lam _ (ih π)

/-- **Theorem 10** [Norrish2007a], equivariance of `→d'`: `π · t →d' π · u ⇔ t →d' u`. The
backward direction follows from the forward one because all permutations have inverses. -/
theorem DBeta'.equivariant (π : FinPerm) (t u : Term) : (π • t) →d' (π • u) ↔ t →d' u := by
  refine ⟨fun h => ?_, fun h => h.dpm π⟩
  simpa only [inv_smul_smul] using h.dpm π⁻¹

end Cslib.LambdaCalculus.Unscoped.Untyped
