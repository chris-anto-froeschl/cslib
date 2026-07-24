/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties
public import Cslib.Languages.LambdaCalculus.Named.Untyped.SwapProperties

/-! # Equivalence of α-equivalence definitions

Theorems showing equivalence of the five definitions of α-equivalence from [Crole2012]:

* `∼p`  (Definition 3.1): permutation with non-occurrence side condition (`AlphaEquiv`)
* `∼p#` (Definition 3.2): permutation with freshness side condition (`AlphaEquivPFresh`)
* `∼¹p` (Definition 3.3): permutation with non-occurrence on bodies only (`AlphaEquivP1`)
* `∼r`  (Definition 3.4): traditional renaming axiom with non-occurrence (`AlphaEquivR`)
* `∼r#` (Definition 3.5): renaming axiom with freshness (`AlphaEquivRFresh`)

The main results are:

* **Theorem 4.1** [Crole2012]: `∼p = ∼p#` (`alphaEquiv_iff_alphaEquivPFresh`)
* **Theorem 4.2** [Crole2012]: `∼p = ∼¹p` (`alphaEquiv_iff_alphaEquivP1`)
* **Theorem 4.4** [Crole2012]: `∼p = ∼r`  (`alphaEquiv_iff_alphaEquivR`)
* **Theorem 4.5** [Crole2012]: `∼p = ∼r#` (`alphaEquiv_iff_alphaEquivRFresh`)
* **Theorem 4.6** [Crole2012]: `∼r = ∼r#` (`alphaEquivR_iff_alphaEquivRFresh`)

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012]
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped.Term

omit [HasFresh Var] in
/-- Non-occurrence obviously implies freshness, and the `swap` operation coincides with
`rename` when the target variable does not occur in the term.
-/
lemma alphaEquiv_of_alphaEquivPFresh {m n : Term Var} : AlphaEquiv m n → AlphaEquivPFresh m n := by
  intro h
  induction h with
  | var => constructor
  | abs z_h1 ih1 ih2 =>
    rename_i x z x1 x2 m1 m2
    have h1 : z ∉ ({x1, x2} : Finset Var) ∪ m1.fv ∪ m2.fv := by
      simp_all [vars_either_fv_or_bv]
    have h2 : AlphaEquivPFresh (m1.swap x1 z) (m2.swap x2 z) := by
      grind [swap_eq_rename_of_not_mem_vars]
    apply AlphaEquivPFresh.abs h1 h2
  | app h1 h2 ih1 ih2 => exact AlphaEquivPFresh.app ih1 ih2

lemma alphaEquivPFresh_of_alphaEquiv {m n : Term Var} : AlphaEquivPFresh m n → AlphaEquiv m n := by
  intro h
  induction h with
  | var => constructor
  | abs hy _h ih =>
    rename_i u a b E E'
    -- We have: (u a) · E ∼p (u b) · E' (by induction: ih) and u # a, b, E, E' (by hy).
    -- Extract freshness conditions from hy.
    have hu_E : u ∉ E.fv := by aesop
    have hu_E' : u ∉ E'.fv := by aesop
    -- Pick z ≠ u with z ∉ vars(E) ∪ vars(E') ∪ {a, b} (stronger than freshness).
    obtain ⟨z, hz⟩ : ∃ z : Var, z ∉ E.vars ∪ E'.vars ∪ {a, b, u} := by
      exact Infinite.exists_notMem_finset (E.vars ∪ E'.vars ∪ {a, b, u})
    have hz_E : z ∉ E.vars := by aesop
    have hz_E' : z ∉ E'.vars := by aesop
    have hz_fv_E : z ∉ E.fv := by simp_all [vars_either_fv_or_bv]
    have hz_fv_E' : z ∉ E'.fv := by simp_all [vars_either_fv_or_bv]
    -- Using Lemma 6.1 we get
    have h_swap : ((E.swap u a).swap z u) =α ((E'.swap u b).swap z u) := by
      nth_rw 2 [swap_comm]
      nth_rw 4 [swap_comm]
      exact AlphaEquiv.swap_preserve ih
    -- From Lemma 6.2 part 2 via agreement sets
    have h_agree_E : ((E.swap u a).swap z u) =α (E.swap z a) :=
      swap_comp_alphaEquiv_of_not_mem_fv hu_E hz_fv_E
    have h_agree_E' : ((E'.swap u b).swap z u) =α (E'.swap z b) :=
      swap_comp_alphaEquiv_of_not_mem_fv hu_E' hz_fv_E'
    -- Chain by symmetry and transitivity of ∼p
    -- (z a) · E ∼p (z u)·(u a)·E ∼p (z u)·(u b)·E' ∼p (z b) · E'
    have h_chain : (E.swap z a) =α (E'.swap z b) :=
      AlphaEquiv.trans (AlphaEquiv.symm h_agree_E) (AlphaEquiv.trans h_swap h_agree_E')
    -- Convert swap to rename (since z ∉ vars) and apply the pi rule.
    -- Since z ∉ vars(E), swap z a = rename a z (by swap_comm + swap_eq_rename).
    rw [swap_comm, swap_eq_rename_of_not_mem_vars hz_E] at h_chain
    rw [swap_comm, swap_eq_rename_of_not_mem_vars hz_E'] at h_chain
    exact AlphaEquiv.abs (by aesop) h_chain
  | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2

/-! ## Theorem 4.1 [Crole2012] -/
theorem alphaEquiv_iff_alphaEquivPFresh (m n : Term Var) : AlphaEquiv m n ↔ AlphaEquivPFresh m n :=
  ⟨alphaEquiv_of_alphaEquivPFresh, alphaEquivPFresh_of_alphaEquiv⟩

omit [HasFresh Var] in
lemma alphaEquivP1_of_alphaEquiv {m n : Term Var} : AlphaEquiv m n → AlphaEquivP1 m n := by
  intro h
  induction h with
  | var => constructor
  -- Trivial: `pi` gives `y ∉ m1.vars ∪ m2.vars ∪ {x1, x2}`; `pi1` only needs `y ∉ m1.vars ∪ m2.vars`.
  | abs hy _h ih => exact AlphaEquivP1.abs (by aesop) ih
  | app _ _ ih1 ih2 => exact AlphaEquivP1.app ih1 ih2

lemma alphaEquiv_abs_of_rename_self {m1 m2 : Term Var} {x1 x2 : Var}
  (hx1m2 : x1 ∉ m2.vars)
  (ih : m1 =α (m2.rename x2 x1)) :
  (Term.abs x1 m1) =α (Term.abs x2 m2) := by
    -- Pick any atom `z` with `z ∉ a, b, E, E'`.
    obtain ⟨z, hz⟩ : ∃ z : Var, z ∉ m1.vars ∪ m2.vars ∪ {x1, x2} := Infinite.exists_notMem_finset _
    -- Rewrite `(a b) · E' = E'.rename b a` since `a = x1 ∉ E'.vars` (Definition 3.1 uses `rename`).
    rw [← swap_eq_rename_of_not_mem_vars hx1m2] at ih
    -- Using Lemma 6.1 we get `(z a) · E ∼p (z a) · ((a b) · E')`.
    have h61 := AlphaEquiv.swap_preserve (u := z) (v := x1) ih
    -- From Lemma 6.2 part 1: `(z a) · ((a b) · E') = (z b) · E'` since `z, a ∤ E'`.
    rw [swap_comm (m := m2) (x := x2) (y := x1),
        swap_comp_eq_of_not_mem_vars hx1m2 (by aesop)] at h61
    -- Now `h61 : (z a) · E ∼p (z b) · E'`; appeal to `pi`, converting swaps back to renames.
    apply AlphaEquiv.abs (y := z) (by aesop)
    rw [← swap_eq_rename_of_not_mem_vars (show z ∉ m1.vars by aesop),
        ← swap_eq_rename_of_not_mem_vars (show z ∉ m2.vars by aesop),
        swap_comm (m := m1) (x := x1) (y := z), swap_comm (m := m2) (x := x2) (y := z)]
    exact h61

lemma alphaEquiv_of_alphaEquivP1 {m n : Term Var} : AlphaEquivP1 m n → AlphaEquiv m n := by
  intro h
  induction h with
  | var => constructor
  | abs hy hP1 ih =>
    rename_i u a b E E'
    by_cases hua : u = a
    · subst hua
      -- wlog assume `u = a`
      rw [rename_same] at ih
      exact alphaEquiv_abs_of_rename_self (by aesop) ih
    · by_cases hub : u = b
      · -- Case `u = b`: symmetric to the previous case, using symmetry of `∼p`.
        subst hub
        rw [rename_same] at ih
        exact AlphaEquiv.symm (alphaEquiv_abs_of_rename_self (by aesop) (AlphaEquiv.symm ih))
      · -- Case `u ≠ b`: `u ∉ E.vars ∪ E'.vars ∪ {a, b}`, so appeal directly to `pi`.
        exact AlphaEquiv.abs (y := u) (by aesop) ih
  | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2

/-! ## Theorem 4.2 [Crole2012] -/
theorem alphaEquiv_iff_alphaEquivP1 (m n : Term Var) : AlphaEquiv m n ↔ AlphaEquivP1 m n :=
  ⟨alphaEquivP1_of_alphaEquiv, alphaEquiv_of_alphaEquivP1⟩

/-
/-! ## Theorem 4.4 [Crole2012] -/
theorem alphaEquiv_iff_alphaEquivR (m n : Term Var) :
    AlphaEquiv m n ↔ AlphaEquivR m n := by
  sorry

/-! ## Theorem 4.5 [Crole2012] -/
theorem alphaEquiv_iff_alphaEquivRFresh (m n : Term Var) :
    AlphaEquiv m n ↔ AlphaEquivRFresh m n := by
  sorry

/-! ## Theorem 4.6 [Crole2012] -/
theorem alphaEquivR_iff_alphaEquivRFresh (m n : Term Var) :
    AlphaEquivR m n ↔ AlphaEquivRFresh m n := by
  sorry
-/

end LambdaCalculus.Named.Untyped.Term

end Cslib
