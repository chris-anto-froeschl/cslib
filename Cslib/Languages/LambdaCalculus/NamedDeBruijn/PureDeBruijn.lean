/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Unscoped.Untyped.BetaReduction
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image

/-! # de Bruijn

Covers the material of the [Norrish2007a] Section 2.2 and the first half of Section 4.1.

## The paper's `dB` versus Cslib's `Unscoped.Untyped.Term`

The paper's type `dB` (equation (2)) is the free algebra `ℕ + dB × dB + dB` with constructors
`dV`, `dAPP`, `dABS`.  This is exactly `Cslib.LambdaCalculus.Unscoped.Untyped.Term`, with

| Paper           | Cslib                                       |
|-----------------|---------------------------------------------|
| `dV i`          | `Term.var i`                                |
| `dAPP t u`      | `Term.app t u`                              |
| `dABS t`        | `Term.abs t`                                |
| `lift t k`      | `Term.lift t k` (`= Term.incre 1 k t`)      |
| `nsub z k t`    | `Term.nsub z k t` (`= Term.sub t k z`)      |
| `sub z k t`     | `Term.dsub z k t` (`= Term.subst k z t`)    |
| `dFV t`         | `Term.dFV t`                                |
| `dLAM i t`      | `Term.dLAM i t`                             |
| `→d`  (Def. 1)  | `Beta` (`Unscoped.Untyped.BetaReduction`)   |
| `→d'` (Def. 7)  | `DBeta'`                                    |

The two functions of Nipkow's formalisation (the paper's Figure 2) and the paper's "clean"
substitution (Definition 4) are already present in Cslib under different names; the
abbreviations `lift`, `nsub` and `dsub` introduced below are definitional aliases, and the
lemmas `lift_var`, `nsub_var`, ... are the defining equations in the shape used by the paper.

## Main definitions

* `Term.lift`, `Term.nsub`, `Term.dsub` : paper Figure 2 and Definition 4.
* `Term.dFV` : the set of free indices of a de Bruijn term.
* `Term.dLAM` : **Definition 5**, abstraction over a particular index.
* `DBeta'` : **Definition 7**, the β-reduction relation `→d'` of the intermediate formalism `dB'`.

## Main statements

* `Term.onto_lemma`, `Term.dABS_renamed` : **Lemma 6**, every `dABS`-term is a `dLAM`-term over
  any sufficiently fresh index.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do
  Work*][Norrish2007a]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.Unscoped.Untyped

namespace Term

/-- `lift t k` (paper, Figure 2): add one to all free indices of `t` that are at least `k`.
This is Cslib's `Term.incre 1 k`. -/
abbrev lift (t : Term) (k : ℕ) : Term := incre 1 k t

/-- Figure 2: `lift` on `dV` (HOL `lift_def`). -/
@[simp] lemma lift_var (i k : ℕ) : lift (var i) k = if i < k then var i else var (i + 1) := by
  by_cases h : k ≤ i <;> simp [lift, incre, h]

/-- Figure 2: `lift` on `dAPP` (HOL `lift_def`). -/
@[simp] lemma lift_app (t u : Term) (k : ℕ) : lift (app t u) k = app (lift t k) (lift u k) :=
  rfl

/-- Figure 2: `lift` on `dABS` (HOL `lift_def`). -/
@[simp] lemma lift_abs (t : Term) (k : ℕ) : lift (abs t) k = abs (lift t (k + 1)) := rfl

/-- `nsub z k t` (paper, Figure 2): Nipkow's substitution, which simultaneously substitutes `z`
for the index `k` and decrements all larger free indices.  This is Cslib's `Term.sub`, with the
arguments in the order used by the paper. -/
abbrev nsub (z : Term) (k : ℕ) (t : Term) : Term := t.sub k z

/-- Figure 2: `nsub` on `dV` (HOL `nsub_def`). -/
lemma nsub_var (z : Term) (k i : ℕ) :
    nsub z k (var i) = if k < i then var (i - 1) else if i = k then z else var i := by
  rcases lt_trichotomy i k with h | h | h
  · simp [nsub, var_lt_sub h, Nat.not_lt.mpr h.le, Nat.ne_of_lt h]
  · simp [nsub, h]
  · simp [nsub, var_gt_sub h, h]

/-- Figure 2: `nsub` on `dAPP` (HOL `nsub_def`). -/
lemma nsub_app (z : Term) (k : ℕ) (t u : Term) :
    nsub z k (app t u) = app (nsub z k t) (nsub z k u) := rfl

/-- Figure 2: `nsub` on `dABS` (HOL `nsub_def`). -/
lemma nsub_abs (z : Term) (k : ℕ) (t : Term) :
    nsub z k (abs t) = abs (nsub (lift z 0) (k + 1) t) := abs_sub_zero

/-- **Definition 4**: `dsub z k t` (the paper's `sub`) substitutes `z` for the index `k` in `t`,
without decrementing the other free indices.  An alias for `Term.subst` with the paper's argument
order. -/
abbrev dsub (z : Term) (k : ℕ) (t : Term) : Term := subst k z t

/-- Definition 4: `sub` on `dV` (HOL `sub_def`). -/
@[simp] lemma dsub_var (z : Term) (k i : ℕ) : dsub z k (var i) = if i = k then z else var i :=
  rfl

/-- Definition 4: `sub` on `dAPP` (HOL `sub_def`). -/
@[simp] lemma dsub_app (z : Term) (k : ℕ) (t u : Term) :
    dsub z k (app t u) = app (dsub z k t) (dsub z k u) := rfl

/-- Definition 4: `sub` on `dABS` (HOL `sub_def`). -/
lemma dsub_abs (z : Term) (k : ℕ) (t : Term) :
    dsub z k (abs t) = abs (dsub (lift z 0) (k + 1) t) := rfl

/-- The set of free indices of a de Bruijn term (HOL `dFV_def`). -/
def dFV : Term → Finset ℕ
  | var i => {i}
  | app t u => dFV t ∪ dFV u
  | abs t => ((dFV t).erase 0).image (· - 1)

/-- The free index of `dV i` is `i` (HOL `IN_dFV_thm`). -/
@[simp] lemma mem_dFV_var (i j : ℕ) : j ∈ dFV (var i) ↔ i = j := by
  simp [dFV, eq_comm]

/-- The free indices of an application (HOL `IN_dFV_thm`). -/
@[simp] lemma mem_dFV_app (t u : Term) (j : ℕ) : j ∈ dFV (app t u) ↔ j ∈ dFV t ∨ j ∈ dFV u := by
  simp [dFV]

/-- HOL `IN_dFV_thm`, the `dABS` case. -/
@[simp] lemma mem_dFV_abs (t : Term) (j : ℕ) : j ∈ dFV (abs t) ↔ j + 1 ∈ dFV t := by
  constructor
  · intro h
    simp only [dFV, Finset.mem_image, Finset.mem_erase] at h
    obtain ⟨k, ⟨hk0, hk⟩, rfl⟩ := h
    rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
  · intro h
    simp only [dFV, Finset.mem_image, Finset.mem_erase]
    exact ⟨j + 1, ⟨by omega, h⟩, by omega⟩

/-- The free indices of a lifted term (HOL `IN_dFV_lift`). -/
lemma mem_dFV_lift (t : Term) (n j : ℕ) :
    j ∈ dFV (lift t n) ↔ (j < n ∧ j ∈ dFV t) ∨ (n < j ∧ j - 1 ∈ dFV t) := by
  induction t generalizing n j with
  | var i =>
      grind [lift_var, mem_dFV_var]
  | app t u iht ihu =>
      simp only [lift_app, mem_dFV_app, iht, ihu]
      tauto
  | abs t ih =>
      simp only [lift_abs, mem_dFV_abs, ih, Nat.add_sub_cancel]
      grind

/-- The free indices of a `dsub`-substitution (compare HOL `dFVs_sub`). -/
lemma mem_dFV_dsub (z : Term) (k : ℕ) (t : Term) (j : ℕ) :
    j ∈ dFV (dsub z k t) ↔ (j ∈ dFV t ∧ j ≠ k) ∨ (k ∈ dFV t ∧ j ∈ dFV z) := by
  induction t generalizing z k j with
  | var i =>
      grind [dsub_var, mem_dFV_var]
  | app t u iht ihu =>
      simp only [dsub_app, mem_dFV_app, iht, ihu]
      tauto
  | abs t ih =>
      simp only [dsub_abs, mem_dFV_abs, ih, mem_dFV_lift]
      grind

/-- Substituting for an index that does not occur free changes nothing. -/
lemma dsub_of_not_mem_dFV {t : Term} {k : ℕ} (h : k ∉ dFV t) (z : Term) : dsub z k t = t := by
  induction t generalizing z k with
  | var m => grind [dsub_var, mem_dFV_var]
  | app t₁ t₂ ih₁ ih₂ =>
      simp only [mem_dFV_app, not_or] at h
      simp only [dsub_app, ih₁ h.1, ih₂ h.2]
  | abs t ih =>
      simp only [mem_dFV_abs] at h
      simp only [dsub_abs, ih h]

/-- The number of nodes of a de Bruijn term (HOL `dbsize`).  Unlike `sizeOf`, it does not count
the numerals in `var` nodes, which `lift` and `dsub` change. -/
def dbsize : Term → ℕ
  | var _ => 1
  | app t u => dbsize t + dbsize u + 1
  | abs t => dbsize t + 1

/-- `dbsize` on `dV` (HOL `dbsize_def`). -/
@[simp] lemma dbsize_var (i : ℕ) : dbsize (var i) = 1 := rfl

/-- `dbsize` on `dAPP` (HOL `dbsize_def`). -/
@[simp] lemma dbsize_app (t u : Term) : dbsize (app t u) = dbsize t + dbsize u + 1 := rfl

/-- `dbsize` on `dABS` (HOL `dbsize_def`). -/
@[simp] lemma dbsize_abs (t : Term) : dbsize (abs t) = dbsize t + 1 := rfl

/-- Lifting preserves `dbsize` (HOL `dbsize_lift`). -/
lemma dbsize_lift (t : Term) (n : ℕ) : dbsize (lift t n) = dbsize t := by
  induction t generalizing n with
  | var i => simp only [lift_var]; split_ifs <;> rfl
  | app t u iht ihu => simp [iht, ihu]
  | abs t ih => simp [ih]

/-- Substituting a variable preserves `dbsize` (compare HOL `dbsize_sub`). -/
lemma dbsize_dsub_var (k j : ℕ) (t : Term) : dbsize (dsub (var k) j t) = dbsize t := by
  induction t generalizing k j with
  | var m => simp only [dsub_var]; split_ifs <;> rfl
  | app t u iht ihu => simp [iht, ihu]
  | abs t ih => simp only [dsub_abs, dbsize_abs, lift_var]; split_ifs <;> simp [ih]

/-- **Definition 5**: `dLAM i t` abstracts the free index `i` of `t`.  Like `LAM` on `Λα`, it is
not injective. -/
def dLAM (i : ℕ) (t : Term) : Term := abs (dsub (var 0) (i + 1) (lift t 0))

/-- The induction behind Lemma 6 (HOL `onto_lemma`): if `i` is not free in `t`, then `t` is a
substitution of `dV n` for `i` in a lifted term. -/
lemma onto_lemma (t : Term) (i n : ℕ) (h : i ∉ dFV t) :
    ∃ t₀, t = dsub (var n) i (lift t₀ n) := by
  induction t generalizing i n with
  | var m =>
      simp only [mem_dFV_var] at h
      rcases eq_or_ne m n with rfl | hmn
      · rcases lt_or_ge i m with hi | hi
        · exact ⟨var i, by grind [lift_var, dsub_var]⟩
        · exact ⟨var (i - 1), by grind [lift_var, dsub_var]⟩
      · rcases lt_or_ge m n with hm | hm
        · exact ⟨var m, by grind [lift_var, dsub_var]⟩
        · exact ⟨var (m - 1), by grind [lift_var, dsub_var]⟩
  | app t u iht ihu =>
      simp only [mem_dFV_app, not_or] at h
      obtain ⟨t₀, ht⟩ := iht i n h.1
      obtain ⟨u₀, hu⟩ := ihu i n h.2
      exact ⟨app t₀ u₀, by rw [lift_app, dsub_app, ← ht, ← hu]⟩
  | abs t ih =>
      simp only [mem_dFV_abs] at h
      obtain ⟨t₀, ht⟩ := ih (i + 1) (n + 1) h
      refine ⟨abs t₀, ?_⟩
      rw [lift_abs, dsub_abs, lift_var, ite_eq_right (Nat.not_lt_zero _), ht]

/-- HOL `onto_lemma2`: the free indices of a term are bounded. -/
lemma dFV_bounded (t : Term) : ∃ j, ∀ i ∈ dFV t, i < j := by
  induction t with
  | var i => exact ⟨i + 1, by grind [mem_dFV_var]⟩
  | app t u iht ihu =>
      obtain ⟨j₁, h₁⟩ := iht
      obtain ⟨j₂, h₂⟩ := ihu
      refine ⟨max j₁ j₂, fun k hk => ?_⟩
      simp only [mem_dFV_app] at hk
      grind
  | abs t ih =>
      obtain ⟨j, hj⟩ := ih
      refine ⟨j, fun k hk => ?_⟩
      grind [mem_dFV_abs]

/-- HOL `dfresh_exists`: every de Bruijn term has a fresh index. -/
lemma dfresh_exists (t : Term) : ∃ i, i ∉ dFV t := by
  obtain ⟨j, hj⟩ := dFV_bounded t
  exact ⟨j, fun h => lt_irrefl j (hj j h)⟩

/-- **Lemma 6** (HOL `dABS_renamed`): if `i` is not free in `dABS t`, then `dABS t = dLAM i t₀`
for some `t₀`. -/
lemma dABS_renamed {t : Term} {i : ℕ} (h : i ∉ dFV (abs t)) : ∃ t₀, abs t = dLAM i t₀ := by
  obtain ⟨t₀, ht⟩ := onto_lemma t (i + 1) 0 (by simpa using h)
  exact ⟨t₀, by rw [dLAM, ← ht]⟩

/-- The free indices of a `dLAM`-abstraction (HOL `dFVs_dLAM`). -/
lemma dFV_dLAM (i : ℕ) (t : Term) : dFV (dLAM i t) = (dFV t).erase i := by
  ext j
  simp only [dLAM, mem_dFV_abs, mem_dFV_dsub, mem_dFV_lift, mem_dFV_var, Finset.mem_erase]
  grind

/-- Lifting commutes with substitution (the de Bruijn bookkeeping behind `dsub_dLAM`). -/
lemma lift_dsub (z : Term) (n j : ℕ) (t : Term) :
    lift (dsub z j t) n = dsub (lift z n) (if j < n then j else j + 1) (lift t n) := by
  induction t generalizing z n j with
  | var m => grind [lift_var, dsub_var]
  | app t u iht ihu => simp [iht, ihu]
  | abs t ih =>
      have hidx : (if j + 1 < n + 1 then j + 1 else j + 1 + 1)
          = (if j < n then j else j + 1) + 1 := by split_ifs <;> omega
      simp only [dsub_abs, lift_abs, ih, incre_comm_zero, hidx]

/-- Two `dsub` substitutions for distinct indices commute, provided neither substituted term
contains the other's index free (a special case of HOL `sub_lemma`). -/
lemma dsub_dsub_comm {a b : Term} {k l : ℕ} (hkl : k ≠ l) (hb : k ∉ dFV b) (ha : l ∉ dFV a)
    (u : Term) : dsub a k (dsub b l u) = dsub b l (dsub a k u) := by
  induction u generalizing a b k l with
  | var m =>
      simp only [dsub_var]
      rcases eq_or_ne m l with rfl | hml
      · simp only [ite_true, hkl.symm, ite_false, dsub_var, dsub_of_not_mem_dFV hb]
      · rcases eq_or_ne m k with rfl | hmk
        · simp only [hml, ite_false, ite_true, dsub_var, dsub_of_not_mem_dFV ha]
        · simp only [hml, hmk, ite_false, dsub_var]
  | app u₁ u₂ ih₁ ih₂ => simp only [dsub_app, ih₁ hkl hb ha, ih₂ hkl hb ha]
  | abs u ih =>
      simp only [dsub_abs, ih (a := lift a 0) (b := lift b 0) (by omega : k + 1 ≠ l + 1)
        (by grind [mem_dFV_lift]) (by grind [mem_dFV_lift])]

/-- `dLAM` adds one node. -/
lemma dbsize_dLAM (i : ℕ) (t : Term) : dbsize (dLAM i t) = dbsize t + 1 := by
  simp [dLAM, dbsize_lift, dbsize_dsub_var]

/-- HOL `sub_dLAM`: substitution interacts with `dLAM` as it does with `LAM` in `Λα`. -/
lemma dsub_dLAM {z : Term} {i j : ℕ} {t : Term} (hij : i ≠ j) (hi : i ∉ dFV z) :
    dsub z j (dLAM i t) = dLAM i (dsub z j t) := by
  simp only [dLAM, dsub_abs]
  rw [dsub_dsub_comm (a := lift z 0) (b := var 0) (k := j + 1) (l := i + 1)
      (by omega) (by simp) (by grind [mem_dFV_lift]), lift_dsub]
  simp only [Nat.not_lt_zero, ite_false]

end Term

open Term in
/-- **Definition 7**: β-reduction `→d'` of `dB'`, stated like β on `Λα` with `dLAM` in place of
`LAM`. -/
inductive DBeta' : Term → Term → Prop where
  /-- Contraction: `dAPP (dLAM i t) u →d' sub u i t`. -/
  | red (i : ℕ) (t u : Term) : DBeta' (app (dLAM i t) u) (dsub u i t)
  /-- Congruence in the left argument of an application. -/
  | appL {t u : Term} (z : Term) : DBeta' t u → DBeta' (app t z) (app u z)
  /-- Congruence in the right argument of an application. -/
  | appR {t u : Term} (z : Term) : DBeta' t u → DBeta' (app z t) (app z u)
  /-- Congruence under a `dLAM`-abstraction. -/
  | lam {t u : Term} (i : ℕ) : DBeta' t u → DBeta' (dLAM i t) (dLAM i u)

@[inherit_doc] scoped infix:39 " →d' " => DBeta'

end Cslib.LambdaCalculus.Unscoped.Untyped
