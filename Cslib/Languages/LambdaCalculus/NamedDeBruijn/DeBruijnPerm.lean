/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.PureDeBruijn
public import Cslib.Logics.Nominal.Support

/-! # de Bruijn terms are a nominal set (paper, Sections 3 and 4.2)

This file formalises the paper's Section 3 (*Nominal Reasoning*) instantiated at the type of
pure de Bruijn terms, and the first part of Section 4.2 (*dB' vs λNα: Nominal Reasoning with
Indices*), up to and including **Theorem 10**.

## Permutations

The paper represents a permutation as a list of pairs of strings (Definition 2), and therefore
has to state the third nominal axiom of (4) extensionally.  Cslib's nominal library instead uses
`CatCrypt.Nominal.FinPerm`, the group of finitely supported bijections of `Atom`; the
extensionality axiom of (4) is then automatic, and the nominal-set axioms of (4) are exactly the
`MulAction FinPerm` laws.

Atoms are (wrapped) natural numbers, so the bijection between "strings" and numbers used
throughout Section 4 of the paper is `Atom.ofNat`/`Atom.val`:

| Paper  | Cslib          |
|--------|----------------|
| `î`    | `Atom.ofNat i` |
| `ŝ`    | `s.val`        |

## Main definitions

* `Term.gincAtom` : the guarded increment `ginc` of an atom (HOL `ginc_def`).
* `Term.incPerm` : `inc_g`, the increment of a permutation (**Definition 8**, generalised to an
  arbitrary guard as required for **Lemma 9**).
* `Term.dpm` : the permutation action on de Bruijn terms (**Definition 8**), packaged as the
  `MulAction FinPerm Term` instance, together with the `NomSet Term` instance whose support is
  the set of free indices.

## Main statements

* `Term.lift_dpm` : **Lemma 9** (permutations and `lift`).
* `Term.dpm_dsub`, `Term.dpm_dLAM`, `DBeta'.equivariant` : **Theorem 10** (`sub` and `dLAM` have
  empty support; `→d'` is equivariant).

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*][NV2007]
* [Andrew M. Pitts, *Alpha-structural recursion and induction*][Pitts2006]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.Unscoped.Untyped

open CatCrypt.Nominal

namespace Term

/-! ### Guarded increment of atoms (HOL `ginc`) -/

/-- `gincAtom g a` (HOL `ginc_def`): the atom `a` is untouched if the corresponding index is
less than the guard `g`, and bumped by one otherwise. -/
def gincAtom (g : ℕ) (a : Atom) : Atom := if a.val < g then a else ⟨a.val + 1⟩

/-- The inverse of `gincAtom g` on its image (which is everything but the atom `ĝ`). -/
def gdecAtom (g : ℕ) (a : Atom) : Atom := if a.val ≤ g then a else ⟨a.val - 1⟩

@[simp] theorem gdecAtom_gincAtom (g : ℕ) (a : Atom) : gdecAtom g (gincAtom g a) = a := by
  by_cases h : a.val < g
  · simp [gincAtom, gdecAtom, h, Nat.le_of_lt h]
  · have h' : ¬ (a.val + 1 ≤ g) := by omega
    simp [gincAtom, gdecAtom, h, h']

/-- HOL `ginc_neq`: `ginc` never hits the guard. -/
@[simp] theorem gincAtom_ne (g : ℕ) (a : Atom) : (gincAtom g a).val ≠ g := by
  by_cases h : a.val < g <;> simp [gincAtom, h] <;> omega

theorem gincAtom_gdecAtom {g : ℕ} {a : Atom} (h : a.val ≠ g) : gincAtom g (gdecAtom g a) = a := by
  rcases lt_trichotomy a.val g with hlt | heq | hgt
  · simp [gincAtom, gdecAtom, hlt, Nat.le_of_lt hlt]
  · exact absurd heq h
  · have h1 : ¬ (a.val ≤ g) := by omega
    have h2 : ¬ (a.val - 1 < g) := by omega
    simp only [gdecAtom, h1, ite_false, gincAtom, h2]
    ext
    simp
    omega

/-! ### Definition 8 — incrementing a permutation -/

/-- The underlying function of `incPerm`: the permutation `π`, transported along the guarded
increment `gincAtom g` and extended by the identity at the guard.  Compare HOL
`lswapstr_inc_pm`, the characterisation of what an incremented permutation does to a string. -/
def incFun (g : ℕ) (π : FinPerm) (a : Atom) : Atom :=
  if a.val = g then a else gincAtom g (π (gdecAtom g a))

theorem incFun_incFun_inv (g : ℕ) (π : FinPerm) (a : Atom) :
    incFun g π (incFun g π⁻¹ a) = a := by
  by_cases h : a.val = g
  · simp [incFun, h]
  · have h1 : (gincAtom g (π⁻¹ (gdecAtom g a))).val ≠ g := gincAtom_ne _ _
    simp only [incFun, h, ite_false, h1, gdecAtom_gincAtom]
    rw [show π (π⁻¹ (gdecAtom g a)) = gdecAtom g a from
      Equiv.apply_symm_apply π.val (gdecAtom g a)]
    exact gincAtom_gdecAtom h

theorem incFun_inv_incFun (g : ℕ) (π : FinPerm) (a : Atom) :
    incFun g π⁻¹ (incFun g π a) = a := by
  have h := incFun_incFun_inv g π⁻¹ a
  rwa [inv_inv] at h

/-- **Definition 8** (increment of a permutation), for an arbitrary guard `g`.  `incPerm 0` is
the paper's `inc`, and `incPerm n` is the paper's `inc n` used in **Lemma 9**. -/
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

@[simp] theorem incPerm_apply (g : ℕ) (π : FinPerm) (a : Atom) :
    incPerm g π a = incFun g π a := by
  simp [incPerm, FinPerm.apply]

/-- The action of an incremented permutation with guard `0`, in terms of indices. -/
theorem incFun_zero_val (π : FinPerm) (v : ℕ) :
    (incFun 0 π (Atom.ofNat v)).val =
      if v = 0 then 0 else (π (Atom.ofNat (v - 1))).val + 1 := by
  simp only [incFun, gincAtom, gdecAtom, Atom.ofNat, Nat.not_lt_zero, ite_false, Nat.le_zero_eq]
  split_ifs with h <;> first | exact h | rfl

/-- `lift` on a variable is the guarded increment of atoms. -/
theorem lift_var_eq (i n : ℕ) : lift (var i) n = var (gincAtom n (Atom.ofNat i)).val := by
  by_cases h : i < n <;> simp [lift_var, gincAtom, Atom.ofNat, h]

/-- Incrementing the identity permutation gives the identity. -/
@[simp] theorem incPerm_one (g : ℕ) : incPerm g 1 = 1 := by
  refine FinPerm.ext (fun a => ?_)
  simp only [incPerm_apply, incFun, FinPerm.one_apply]
  split_ifs with h
  · rfl
  · exact gincAtom_gdecAtom h

/-- Incrementing is multiplicative. -/
theorem incPerm_mul (g : ℕ) (π₁ π₂ : FinPerm) :
    incPerm g (π₁ * π₂) = incPerm g π₁ * incPerm g π₂ := by
  refine FinPerm.ext (fun a => ?_)
  simp only [incPerm_apply, incFun, FinPerm.mul_apply]
  by_cases h : a.val = g
  · simp [h]
  · simp only [h, ite_false, gincAtom_ne, gdecAtom_gincAtom]

/-- The tedious index-manoeuvring result needed in the `dABS` case of **Lemma 9**:
`inc 0 (inc n π) = inc (n+1) (inc 0 π)` (an equality of permutations, not just an extensional
one; compare the paper's remark after Lemma 9). -/
theorem incPerm_zero_incPerm (n : ℕ) (π : FinPerm) :
    incPerm 0 (incPerm n π) = incPerm (n + 1) (incPerm 0 π) := by
  refine FinPerm.ext (fun a => ?_)
  simp only [incPerm_apply, incFun, gincAtom, gdecAtom, Nat.not_lt_zero, ite_false,
    Nat.le_zero_eq]
  split_ifs <;> apply Atom.ext <;> (try dsimp only at *) <;> omega

/-! ### Definition 8 — the permutation action on `dB` -/

/-- **Definition 8** (Permutation for `dB`).  When a permutation passes through an abstraction
the free variables it acts on sit at different index positions, so the permutation has to be
incremented. -/
def dpm (π : FinPerm) : Term → Term
  | var i => var (π (Atom.ofNat i)).val
  | app t u => app (dpm π t) (dpm π u)
  | abs t => abs (dpm (incPerm 0 π) t)

theorem dpm_one (t : Term) : dpm 1 t = t := by
  induction t with
  | var i => simp [dpm]
  | app t u iht ihu => simp [dpm, iht, ihu]
  | abs t ih => simp only [dpm, incPerm_one, ih]

theorem dpm_mul (π₁ π₂ : FinPerm) (t : Term) : dpm (π₁ * π₂) t = dpm π₁ (dpm π₂ t) := by
  induction t generalizing π₁ π₂ with
  | var i => simp [dpm]
  | app t u iht ihu => simp [dpm, iht, ihu]
  | abs t ih => simp only [dpm, incPerm_mul, ih]

/-- de Bruijn terms carry a permutation action, i.e. the conditions (4) of the paper hold. -/
instance : MulAction FinPerm Term where
  smul := dpm
  one_smul := dpm_one
  mul_smul := dpm_mul

@[simp] theorem smul_def (π : FinPerm) (t : Term) : π • t = dpm π t := rfl

@[simp] theorem dpm_var (π : FinPerm) (i : ℕ) : π • var i = var (π (Atom.ofNat i)).val := rfl

@[simp] theorem dpm_app (π : FinPerm) (t u : Term) : π • app t u = app (π • t) (π • u) := rfl

@[simp] theorem dpm_abs (π : FinPerm) (t : Term) : π • abs t = abs ((incPerm 0 π) • t) := rfl

/-- The free indices of a permuted term. -/
theorem mem_dFV_dpm (π : FinPerm) (t : Term) (i : ℕ) :
    i ∈ dFV (π • t) ↔ ∃ j ∈ dFV t, (π (Atom.ofNat j)).val = i := by
  induction t generalizing π i with
  | var m =>
      simp only [dpm_var, mem_dFV_var]
      constructor
      · rintro rfl; exact ⟨m, rfl, rfl⟩
      · rintro ⟨j, hj, rfl⟩; rw [hj]
  | app t u iht ihu =>
      simp only [dpm_app, mem_dFV_app, iht, ihu]
      constructor
      · rintro (⟨j, hj, hv⟩ | ⟨j, hj, hv⟩) <;> exact ⟨j, by simp [hj], hv⟩
      · rintro ⟨j, hj, hv⟩
        rcases hj with hj | hj
        · exact Or.inl ⟨j, hj, hv⟩
        · exact Or.inr ⟨j, hj, hv⟩
  | abs t ih =>
      simp only [dpm_abs, mem_dFV_abs, ih]
      constructor
      · rintro ⟨j, hj, hv⟩
        rw [incPerm_apply, incFun_zero_val] at hv
        split_ifs at hv with h0
        refine ⟨j - 1, ?_, by omega⟩
        have hjj : j - 1 + 1 = j := by omega
        rwa [hjj]
      · rintro ⟨j, hj, hv⟩
        refine ⟨j + 1, hj, ?_⟩
        rw [incPerm_apply, incFun_zero_val]
        simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, hv]

/-- The support of a de Bruijn term is its set of free indices, converted into atoms via the
hat-isomorphism (paper, Section 4.2; HOL `dpm_supp`). -/
theorem supports_dFV (t : Term) : Supports ((dFV t).image Atom.ofNat) t := by
  intro π hπ
  induction t generalizing π with
  | var i =>
      have hfix : π (Atom.ofNat i) = Atom.ofNat i := hπ _ (by simp)
      rw [dpm_var, hfix]
      rfl
  | app t u iht ihu =>
      have h1 := iht π (fun a ha => hπ a (by
        simp only [Finset.mem_image, mem_dFV_app] at ha ⊢
        obtain ⟨j, hj, rfl⟩ := ha
        exact ⟨j, Or.inl hj, rfl⟩))
      have h2 := ihu π (fun a ha => hπ a (by
        simp only [Finset.mem_image, mem_dFV_app] at ha ⊢
        obtain ⟨j, hj, rfl⟩ := ha
        exact ⟨j, Or.inr hj, rfl⟩))
      rw [dpm_app, h1, h2]
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

theorem dFV_dpm (t : Term) (π : FinPerm) :
    (dFV (π • t)).image Atom.ofNat = ((dFV t).image Atom.ofNat).image (π ·) := by
  ext a
  simp only [Finset.mem_image, mem_dFV_dpm]
  constructor
  · rintro ⟨i, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨Atom.ofNat j, ⟨j, hj, rfl⟩, Atom.val_ofNat _⟩
  · rintro ⟨b, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨(π (Atom.ofNat j)).val, ⟨j, hj, rfl⟩, Atom.val_ofNat _⟩

/-- de Bruijn terms form a nominal set, with support the set of free indices. -/
instance : NomSet Term where
  toMulAction := inferInstance
  supp t := (dFV t).image Atom.ofNat
  supp_supports := supports_dFV
  supp_equivariant := dFV_dpm

/-! ### Lemma 9 and Theorem 10 -/

/-- **Lemma 9** (Permutations and `lift`): `lift (π · t) n = (inc n π) · (lift t n)`. -/
theorem lift_dpm (π : FinPerm) (t : Term) (n : ℕ) :
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

/-- **Theorem 10**, substitution part: `sub` has empty support,
`π · (sub t j u) = sub (π · t) (π(ĵ)) (π · u)` (HOL `dpm_sub`). -/
theorem dpm_dsub (π : FinPerm) (t : Term) (j : ℕ) (u : Term) :
    π • (dsub t j u) = dsub (π • t) (π (Atom.ofNat j)).val (π • u) := by
  induction u generalizing π t j with
  | var m =>
      simp only [dsub_var, dpm_var]
      by_cases h : m = j
      · subst h
        simp only [ite_true]
      · have h2 : ¬ ((π (Atom.ofNat m)).val = (π (Atom.ofNat j)).val) := by
          intro he
          exact h (congrArg Atom.val (π.val.injective (Atom.ext he)))
        simp only [h, h2, ite_false, dpm_var]
  | app u₁ u₂ ih₁ ih₂ => simp only [dsub_app, dpm_app, ih₁, ih₂]
  | abs u ih =>
      simp only [dsub_abs, dpm_abs, ih, ← lift_dpm]
      congr 1

/-- **Theorem 10**, abstraction part: `dLAM` has empty support,
`π · (dLAM i t) = dLAM (π(î)) (π · t)` (HOL `dpm_dLAM`). -/
theorem dpm_dLAM (π : FinPerm) (i : ℕ) (t : Term) :
    π • (dLAM i t) = dLAM (π (Atom.ofNat i)).val (π • t) := by
  simp only [dLAM, dpm_abs, dpm_dsub, dpm_var, ← lift_dpm]
  congr 1

end Term

/-- **Theorem 10**, forward direction of the equivariance of `→d'`, by rule induction. -/
theorem DBeta'.dpm {t u : Term} (h : t →d' u) (π : FinPerm) : (π • t) →d' (π • u) := by
  induction h generalizing π with
  | red i t u =>
      rw [Term.dpm_app, Term.dpm_dLAM, Term.dpm_dsub]
      exact DBeta'.red _ _ _
  | appL z _ ih => rw [Term.dpm_app, Term.dpm_app]; exact DBeta'.appL _ (ih π)
  | appR z _ ih => rw [Term.dpm_app, Term.dpm_app]; exact DBeta'.appR _ (ih π)
  | lam i _ ih => rw [Term.dpm_dLAM, Term.dpm_dLAM]; exact DBeta'.lam _ (ih π)

/-- **Theorem 10**, equivariance of `→d'`: `π · t →d' π · u ⇔ t →d' u`.  The backward direction
follows from the forward one because all permutations have inverses. -/
theorem DBeta'.equivariant {t u : Term} (π : FinPerm) : (π • t) →d' (π • u) ↔ t →d' u := by
  refine ⟨fun h => ?_, fun h => h.dpm π⟩
  have h2 := h.dpm π⁻¹
  rwa [inv_smul_smul, inv_smul_smul] at h2

end Cslib.LambdaCalculus.Unscoped.Untyped
