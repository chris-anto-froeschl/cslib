/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Unscoped.Untyped.BetaReduction
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image

/-! # Proof Pearl: de Bruijn terms really do work — the de Bruijn side (`dB` and `dB'`)

This file is part of a formalisation of

* Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*,
  TPHOLs 2007.

It covers the material of the paper's Section 2.2 (*de Bruijn's Anonymous Abstraction, using
Indices*) and the first half of Section 4.1 (*An Intermediate Formalism: dB'*).

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
* `Term.db_cases'` : the `dLAM`-based case analysis for `dB` that makes `dB'` look like `Λα`.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*][NV2007]
* [Tobias Nipkow, *More Church-Rosser proofs (in Isabelle/HOL)*][Nipkow2001]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.Unscoped.Untyped

namespace Term

/-! ### Section 2.2 — Nipkow's `lift` and `nsub` (Figure 2) -/

/-- `lift t k` (paper, Figure 2): add one to all free indices of `t` that are at least `k`.
This is Cslib's `Term.incre 1 k`. -/
abbrev lift (t : Term) (k : ℕ) : Term := incre 1 k t

@[simp] theorem lift_var (i k : ℕ) : lift (var i) k = if i < k then var i else var (i + 1) := by
  by_cases h : k ≤ i <;> simp [lift, incre, h]

@[simp] theorem lift_app (t u : Term) (k : ℕ) : lift (app t u) k = app (lift t k) (lift u k) :=
  rfl

@[simp] theorem lift_abs (t : Term) (k : ℕ) : lift (abs t) k = abs (lift t (k + 1)) := rfl

/-- `nsub z k t` (paper, Figure 2): Nipkow's substitution, which simultaneously substitutes `z`
for the index `k` and decrements all larger free indices.  This is Cslib's `Term.sub`, with the
arguments in the order used by the paper. -/
abbrev nsub (z : Term) (k : ℕ) (t : Term) : Term := t.sub k z

@[simp] theorem nsub_var (z : Term) (k i : ℕ) :
    nsub z k (var i) = if k < i then var (i - 1) else if i = k then z else var i := by
  rcases lt_trichotomy i k with h | h | h
  · simp [nsub, var_lt_sub h, Nat.not_lt.mpr h.le, Nat.ne_of_lt h]
  · simp [nsub, h]
  · simp [nsub, var_gt_sub h, h]

@[simp] theorem nsub_app (z : Term) (k : ℕ) (t u : Term) :
    nsub z k (app t u) = app (nsub z k t) (nsub z k u) := rfl

@[simp] theorem nsub_abs (z : Term) (k : ℕ) (t : Term) :
    nsub z k (abs t) = abs (nsub (lift z 0) (k + 1) t) := abs_sub_zero

/-! ### Section 4.1 — a clean notion of substitution (Definition 4) -/

/-- **Definition 4** (A clean notion of substitution for `dB`): `dsub z k t` substitutes `z` for
the index `k` in `t`, *without* decrementing the other free indices.  This is Cslib's
`Term.subst`, with the arguments in the order used by the paper. -/
abbrev dsub (z : Term) (k : ℕ) (t : Term) : Term := subst k z t

@[simp] theorem dsub_var (z : Term) (k i : ℕ) : dsub z k (var i) = if i = k then z else var i :=
  rfl

@[simp] theorem dsub_app (z : Term) (k : ℕ) (t u : Term) :
    dsub z k (app t u) = app (dsub z k t) (dsub z k u) := rfl

@[simp] theorem dsub_abs (z : Term) (k : ℕ) (t : Term) :
    dsub z k (abs t) = abs (dsub (lift z 0) (k + 1) t) := rfl

/-! ### Free indices -/

/-- The set of free indices of a de Bruijn term (HOL `dFV_def`).  Under the bijection between
strings and numbers this is the support of `t` in the nominal set of de Bruijn terms, see
`Cslib.Languages.LambdaCalculus.NamedDeBruijn.DeBruijnPerm`. -/
def dFV : Term → Finset ℕ
  | var i => {i}
  | app t u => dFV t ∪ dFV u
  | abs t => ((dFV t).erase 0).image (· - 1)

@[simp] theorem mem_dFV_var (i j : ℕ) : j ∈ dFV (var i) ↔ i = j := by
  simp [dFV, eq_comm]

@[simp] theorem mem_dFV_app (t u : Term) (j : ℕ) : j ∈ dFV (app t u) ↔ j ∈ dFV t ∨ j ∈ dFV u := by
  simp [dFV]

/-- HOL `IN_dFV_thm`, the `dABS` case. -/
@[simp] theorem mem_dFV_abs (t : Term) (j : ℕ) : j ∈ dFV (abs t) ↔ j + 1 ∈ dFV t := by
  constructor
  · intro h
    simp only [dFV, Finset.mem_image, Finset.mem_erase] at h
    obtain ⟨k, ⟨hk0, hk⟩, rfl⟩ := h
    have : k - 1 + 1 = k := by omega
    rwa [this]
  · intro h
    simp only [dFV, Finset.mem_image, Finset.mem_erase]
    exact ⟨j + 1, ⟨by omega, h⟩, by omega⟩

/-- The free indices of a lifted term (HOL `IN_dFV_lift`). -/
theorem mem_dFV_lift (t : Term) (n j : ℕ) :
    j ∈ dFV (lift t n) ↔ (j < n ∧ j ∈ dFV t) ∨ (n < j ∧ j - 1 ∈ dFV t) := by
  induction t generalizing n j with
  | var i =>
      by_cases h : i < n <;> simp only [lift_var, h, ite_true, ite_false, mem_dFV_var] <;>
        constructor <;> intro hh <;> omega
  | app t u iht ihu =>
      simp only [lift_app, mem_dFV_app, iht, ihu]
      tauto
  | abs t ih =>
      simp only [lift_abs, mem_dFV_abs, ih]
      have e : j + 1 - 1 = j := by omega
      rw [e]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨by omega, h2⟩
        · have e2 : j - 1 + 1 = j := by omega
          exact Or.inr ⟨by omega, by rw [e2]; exact h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨by omega, h2⟩
        · have e2 : j - 1 + 1 = j := by omega
          rw [e2] at h2
          exact Or.inr ⟨by omega, h2⟩

/-- The free indices of a `dsub`-substitution (HOL `IN_dFV_sub`). -/
theorem mem_dFV_dsub (z : Term) (k : ℕ) (t : Term) (j : ℕ) :
    j ∈ dFV (dsub z k t) ↔ (j ∈ dFV t ∧ j ≠ k) ∨ (k ∈ dFV t ∧ j ∈ dFV z) := by
  induction t generalizing z k j with
  | var i =>
      by_cases h : i = k <;> simp only [dsub_var, h, ite_true, ite_false, mem_dFV_var] <;>
        constructor <;> intro hh <;> first | tauto | omega
  | app t u iht ihu =>
      simp only [dsub_app, mem_dFV_app, iht, ihu]
      tauto
  | abs t ih =>
      simp only [dsub_abs, mem_dFV_abs, ih, mem_dFV_lift]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, by omega⟩
        · rcases h2 with ⟨hlt, _⟩ | ⟨_, h4⟩
          · omega
          · exact Or.inr ⟨h1, by simpa using h4⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, by omega⟩
        · exact Or.inr ⟨h1, Or.inr ⟨by omega, by simpa using h2⟩⟩

/-- Substituting for an index that does not occur free changes nothing. -/
theorem dsub_of_not_mem_dFV {t : Term} {k : ℕ} (h : k ∉ dFV t) (z : Term) : dsub z k t = t := by
  induction t generalizing z k with
  | var m => simp only [mem_dFV_var] at h; simp only [dsub_var]; split_ifs; rfl
  | app t₁ t₂ ih₁ ih₂ =>
      simp only [mem_dFV_app, not_or] at h
      simp only [dsub_app, ih₁ h.1, ih₂ h.2]
  | abs t ih => simp only [mem_dFV_abs] at h; simp only [dsub_abs, ih h]

/-! ### Size

The structural size of a de Bruijn term (HOL `dbsize`).  `sizeOf` cannot be used for the
complete-induction argument behind the surjectivity of `f` (`fromTerm_surjective`), because it
counts the numerals stored in `dV`-nodes, which `lift` and `sub` change. -/

/-- The number of nodes of a de Bruijn term (HOL `dbsize`). -/
def dbsize : Term → ℕ
  | var _ => 1
  | app t u => dbsize t + dbsize u + 1
  | abs t => dbsize t + 1

@[simp] theorem dbsize_var (i : ℕ) : dbsize (var i) = 1 := rfl

@[simp] theorem dbsize_app (t u : Term) : dbsize (app t u) = dbsize t + dbsize u + 1 := rfl

@[simp] theorem dbsize_abs (t : Term) : dbsize (abs t) = dbsize t + 1 := rfl

@[simp] theorem dbsize_lift (t : Term) (n : ℕ) : dbsize (lift t n) = dbsize t := by
  induction t generalizing n with
  | var i => simp only [lift_var]; split_ifs <;> rfl
  | app t u iht ihu => simp [iht, ihu]
  | abs t ih => simp [ih]

@[simp] theorem dbsize_dsub_var (k j : ℕ) (t : Term) : dbsize (dsub (var k) j t) = dbsize t := by
  induction t generalizing k j with
  | var m => simp only [dsub_var]; split_ifs <;> rfl
  | app t u iht ihu => simp [iht, ihu]
  | abs t ih => simp only [dsub_abs, dbsize_abs, lift_var]; split_ifs <;> simp [ih]

/-! ### Section 4.1 — abstraction over an index (Definition 5) -/

/-- **Definition 5** (Abstraction over an index): `dLAM i t = dABS (sub (dV 0) (i+1) (lift t 0))`.

This constructor is deliberately *not* injective: `dLAM i t` and `dLAM j u` may be equal for
`i ≠ j`, exactly as `LAM` is not injective on the α-quotiented type `Λα`. -/
def dLAM (i : ℕ) (t : Term) : Term := abs (dsub (var 0) (i + 1) (lift t 0))

/-- **Lemma 6**, main induction (HOL `onto_lemma`): if `i` is not free in `t`, then `t` is a
substitution of `dV n` for `i` in a lifted term.  Proved by structural induction on `t`. -/
theorem onto_lemma (t : Term) (i n : ℕ) (h : i ∉ dFV t) :
    ∃ t₀, t = dsub (var n) i (lift t₀ n) := by
  induction t generalizing i n with
  | var m =>
      simp only [mem_dFV_var] at h
      rcases eq_or_ne m n with rfl | hmn
      · rcases lt_or_ge i m with hi | hi
        · refine ⟨var i, ?_⟩
          simp only [lift_var]; split_ifs <;> simp only [dsub_var] <;> split_ifs <;> rfl
        · have hi' : m < i := lt_of_le_of_ne hi h
          refine ⟨var (i - 1), ?_⟩
          simp only [lift_var]; split_ifs <;> simp only [dsub_var] <;> split_ifs <;>
            first | rfl | (congr 1; omega)
      · rcases lt_or_ge m n with hm | hm
        · refine ⟨var m, ?_⟩
          simp only [lift_var]; split_ifs <;> simp only [dsub_var] <;> split_ifs <;> rfl
        · have hm' : n < m := lt_of_le_of_ne hm (Ne.symm hmn)
          refine ⟨var (m - 1), ?_⟩
          simp only [lift_var]; split_ifs <;> simp only [dsub_var] <;> split_ifs <;>
            first | rfl | (congr 1; omega)
  | app t u iht ihu =>
      simp only [mem_dFV_app, not_or] at h
      obtain ⟨t₀, ht⟩ := iht i n h.1
      obtain ⟨u₀, hu⟩ := ihu i n h.2
      exact ⟨app t₀ u₀, by rw [lift_app, dsub_app, ← ht, ← hu]⟩
  | abs t ih =>
      simp only [mem_dFV_abs] at h
      obtain ⟨t₀, ht⟩ := ih (i + 1) (n + 1) h
      refine ⟨abs t₀, ?_⟩
      rw [lift_abs, dsub_abs, lift_var]
      simp only [Nat.not_lt_zero, ite_false]
      exact congrArg abs ht

/-- HOL `onto_lemma2`: the free indices of a term are bounded. -/
theorem dFV_bounded (t : Term) : ∃ j, ∀ i ∈ dFV t, i < j := by
  induction t with
  | var i => exact ⟨i + 1, by intro k hk; simp only [mem_dFV_var] at hk; omega⟩
  | app t u iht ihu =>
      obtain ⟨j₁, h₁⟩ := iht
      obtain ⟨j₂, h₂⟩ := ihu
      refine ⟨max j₁ j₂, fun k hk => ?_⟩
      simp only [mem_dFV_app] at hk
      rcases hk with h | h
      · have := h₁ k h; omega
      · have := h₂ k h; omega
  | abs t ih =>
      obtain ⟨j, hj⟩ := ih
      refine ⟨j, fun k hk => ?_⟩
      simp only [mem_dFV_abs] at hk
      have := hj (k + 1) hk
      omega

/-- HOL `dfresh_exists`: every de Bruijn term has a fresh index. -/
theorem dfresh_exists (t : Term) : ∃ i, i ∉ dFV t := by
  obtain ⟨j, hj⟩ := dFV_bounded t
  exact ⟨j, fun h => absurd (hj j h) (lt_irrefl j)⟩

/-- **Lemma 6** (`dABS` terms as `dLAM` terms, HOL `dABS_renamed`): if `i` is not among the free
indices of `dABS t`, then `dABS t = dLAM i t₀` for some `t₀`; by the definition of `dLAM` and
injectivity of `dABS` we further know `t = sub (dV 0) (i+1) (lift t₀ 0)`. -/
theorem dABS_renamed {t : Term} {i : ℕ} (h : i ∉ dFV (abs t)) : ∃ t₀, abs t = dLAM i t₀ := by
  have h' : i + 1 ∉ dFV t := by simpa using h
  obtain ⟨t₀, ht⟩ := onto_lemma t (i + 1) 0 h'
  exact ⟨t₀, by rw [dLAM, ← ht]⟩

/-- HOL `db_cases'`: a cases theorem for `dB` based around `dLAM` rather than `dABS`.  This is
what makes `dB'` "syntactic sugar for `dB` that looks like `λNα`" (paper, Section 2). -/
theorem db_cases' (t : Term) :
    (∃ i, t = var i) ∨ (∃ t₀ t₁, t = app t₀ t₁) ∨ (∃ i t₀, t = dLAM i t₀) := by
  match t with
  | var i => exact Or.inl ⟨i, rfl⟩
  | app t₀ t₁ => exact Or.inr (Or.inl ⟨t₀, t₁, rfl⟩)
  | abs t' =>
    obtain ⟨i, hi⟩ := dfresh_exists (abs t')
    obtain ⟨t₀, h⟩ := dABS_renamed hi
    exact Or.inr (Or.inr ⟨i, t₀, h⟩)

/-- The free indices of a `dLAM`-abstraction (HOL `dFVs_dLAM`); this is the key fact that makes
the nominal recursion principle applicable in `Theorem 11`. -/
theorem dFV_dLAM (i : ℕ) (t : Term) : dFV (dLAM i t) = (dFV t).erase i := by
  ext j
  simp only [dLAM, mem_dFV_abs, mem_dFV_dsub, mem_dFV_lift, mem_dFV_var, Finset.mem_erase]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rcases h1 with ⟨hlt, _⟩ | ⟨_, h4⟩
      · omega
      · exact ⟨by omega, by simpa using h4⟩
    · omega
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨Or.inr ⟨by omega, by simpa using h2⟩, by omega⟩

/-- Lifting commutes with substitution (the de Bruijn bookkeeping behind `dsub_dLAM`). -/
theorem lift_dsub (z : Term) (n j : ℕ) (t : Term) :
    lift (dsub z j t) n = dsub (lift z n) (if j < n then j else j + 1) (lift t n) := by
  induction t generalizing z n j with
  | var m => by_cases h : m = j <;> simp [h] <;> split_ifs <;> simp_all <;> omega
  | app t u iht ihu => simp [iht, ihu]
  | abs t ih =>
      have hidx : (if j + 1 < n + 1 then j + 1 else j + 1 + 1)
          = (if j < n then j else j + 1) + 1 := by split_ifs <;> omega
      simp only [dsub_abs, lift_abs, ih, incre_comm_zero, hidx]

/-- The substitution lemma for `dsub`: two substitutions for distinct indices commute, provided
neither substituted term contains the other's index free. -/
theorem dsub_dsub_comm {a b : Term} {k l : ℕ} (hkl : k ≠ l) (hb : k ∉ dFV b) (ha : l ∉ dFV a)
    (u : Term) : dsub a k (dsub b l u) = dsub b l (dsub a k u) := by
  induction u generalizing a b k l with
  | var m =>
      simp only [dsub_var]
      rcases eq_or_ne m l with rfl | hml
      · simp only [ite_true, Ne.symm hkl, ite_false, dsub_var, ite_true,
          dsub_of_not_mem_dFV hb]
      · rcases eq_or_ne m k with rfl | hmk
        · simp only [hml, ite_false, ite_true, dsub_var, ite_true, dsub_of_not_mem_dFV ha]
        · simp only [hml, hmk, ite_false, dsub_var]
  | app u₁ u₂ ih₁ ih₂ => simp only [dsub_app, ih₁ hkl hb ha, ih₂ hkl hb ha]
  | abs u ih =>
      have hb' : k + 1 ∉ dFV (lift b 0) := by
        simp only [mem_dFV_lift]
        rintro (⟨h, _⟩ | ⟨_, h⟩)
        · omega
        · exact hb (by simpa using h)
      have ha' : l + 1 ∉ dFV (lift a 0) := by
        simp only [mem_dFV_lift]
        rintro (⟨h, _⟩ | ⟨_, h⟩)
        · omega
        · exact ha (by simpa using h)
      simp only [dsub_abs, ih (by omega : k + 1 ≠ l + 1) hb' ha']

@[simp] theorem dbsize_dLAM (i : ℕ) (t : Term) : dbsize (dLAM i t) = dbsize t + 1 := by
  simp [dLAM]

/-- HOL `sub_dLAM`: substitution interacts with `dLAM` as it does with `LAM` in `Λα`. -/
theorem dsub_dLAM {z : Term} {i j : ℕ} {t : Term} (hij : i ≠ j) (hi : i ∉ dFV z) :
    dsub z j (dLAM i t) = dLAM i (dsub z j t) := by
  have h0 : (j + 1 : ℕ) ∉ dFV (var (0 : ℕ)) := by simp
  have hz : i + 1 ∉ dFV (lift z 0) := by
    simp only [mem_dFV_lift]
    rintro (⟨h, _⟩ | ⟨_, h⟩)
    · omega
    · exact hi (by simpa using h)
  simp only [dLAM, dsub_abs]
  rw [dsub_dsub_comm (a := lift z 0) (b := var 0) (k := j + 1) (l := i + 1)
      (by omega) h0 hz, lift_dsub]
  simp only [Nat.not_lt_zero, ite_false]

end Term

/-! ### Section 4.1 — β-reduction for `dB'` (Definition 7)

Nipkow's relation `→d` (paper, Definition 1) is already available in Cslib as
`Cslib.LambdaCalculus.Unscoped.Untyped.Beta`; note that its contraction rule
`Beta.red : Beta (app (abs t) s) (t.sub 0 s)` is literally `dAPP (dABS t) s →d nsub s 0 t`. -/

open Term in
/-- **Definition 7** (`dB'` β-reduction, `→d'`).  It mimics the traditional statement in the
λ-calculus for both contraction and congruence rules, using `dLAM` in place of `dABS`. -/
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
