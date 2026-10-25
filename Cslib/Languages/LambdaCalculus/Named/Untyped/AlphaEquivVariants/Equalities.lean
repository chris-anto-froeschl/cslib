/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivVariants.Defs
public import Cslib.Languages.LambdaCalculus.Named.Untyped.RenameProperties
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivProperties
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivVariants.Swap
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivVariants.SwapSubst

/-! # Equivalence of α-equivalence definitions

Theorems showing equivalence of the five definitions of α-equivalence from [Crole2012]:

* `∼p`  (Definition 3.1): permutation with non-occurrence side condition (`AlphaEquiv`)
* `∼p#` (Definition 3.2): permutation with freshness side condition (`AlphaEquivPFresh`)
* `∼¹p` (Definition 3.3): permutation with non-occurrence on bodies only (`AlphaEquivP1`)
* `∼r`  (Definition 3.4): traditional renaming axiom with non-occurrence (`AlphaEquivR`)
* `∼r#` (Definition 3.5): renaming axiom with freshness (`AlphaEquivRFresh`)

## Main results

* **Theorem 4.1** [Crole2012]: `∼p = ∼p#` (`alphaEquiv_iff_alphaEquivPFresh`)
* **Theorem 4.2** [Crole2012]: `∼p = ∼¹p` (`alphaEquiv_iff_alphaEquivP1`)
* **Proposition 4.3** [Crole2012]: `∼²p ≠ ∼p` and `∼³p ≠ ∼p` (`alphaEquiv_variants`)
* **Theorem 4.4** [Crole2012]: `∼p = ∼r`  (`alphaEquiv_iff_alphaEquivR`)
* **Theorem 4.5** [Crole2012]: `∼p = ∼r#` (`alphaEquiv_iff_alphaEquivRFresh`)
* **Theorem 4.6** [Crole2012]: `∼r = ∼r#` (`alphaEquivR_iff_alphaEquivRFresh`)

Theorem 4.6 is obtained from Theorems 4.4 and 4.5. Crole's direct proof by renaming alone, which
needs his Lemma 6.7, is stated as `theorem_wanted`.

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
`rename` when the target variable does not occur in the term. -/
lemma alphaEquivPFresh_of_alphaEquiv {m n : Term Var} (h : m =α n) : AlphaEquivPFresh m n := by
  induction h with
  | var => constructor
  | @abs z x1 x2 m1 m2 hz _ ih =>
    have h1 : z ∉ ({x1, x2} : Finset Var) ∪ m1.fv ∪ m2.fv := by
      simp_all [vars_eq_fv_union_bv]
    have h2 : AlphaEquivPFresh (m1.swap x1 z) (m2.swap x2 z) := by
      grind [swap_eq_rename_of_notMem_vars]
    apply AlphaEquivPFresh.abs h1 h2
  | app h1 h2 ih1 ih2 => exact AlphaEquivPFresh.app ih1 ih2

/-- The converse direction: the freshness witness `u` of the rule `pi#` is exchanged for an atom
`z` that does not occur at all, using Lemma 6.1 and Lemma 6.2 part 2 [Crole2012]. -/
lemma alphaEquiv_of_alphaEquivPFresh {m n : Term Var} (h : AlphaEquivPFresh m n) : m =α n := by
  induction h with
  | var => constructor
  | @abs u a b m m' hy _ ih =>
    -- We have: (u a) · m ∼p (u b) · m' (by induction: ih) and u # a, b, m, m' (by hy).
    -- Pick z ≠ u with z ∉ vars(m) ∪ vars(m') ∪ {a, b} (stronger than freshness).
    obtain ⟨z, hz⟩ := fresh_exists (m.vars ∪ m'.vars ∪ {a, b, u})
    have hzm : z ∉ m.vars := by grind
    have hzm' : z ∉ m'.vars := by grind
    -- Using Lemma 6.1 we get
    have h_swap : ((m.swap u a).swap z u) =α ((m'.swap u b).swap z u) := by
      nth_rw 2 [swap_comm]
      nth_rw 4 [swap_comm]
      exact AlphaEquiv.swap_preserve ih
    -- From Lemma 6.2 part 2 via agreement sets
    have h_agree : ((m.swap u a).swap z u) =α (m.swap z a) := by
      apply swap_comp_alphaEquiv_of_notMem_fv <;> grind [vars_eq_fv_union_bv]
    have h_agree' : ((m'.swap u b).swap z u) =α (m'.swap z b) := by
      apply swap_comp_alphaEquiv_of_notMem_fv <;> grind [vars_eq_fv_union_bv]
    -- Chain by symmetry and transitivity of ∼p
    -- (z a) · m ∼p (z u)·(u a)·m ∼p (z u)·(u b)·m' ∼p (z b) · m'
    have h_chain : (m.swap z a) =α (m'.swap z b) := h_agree.symm.trans (h_swap.trans h_agree')
    -- Convert swap to rename (since z ∉ vars) and apply the pi rule.
    -- Since z ∉ vars(m), swap z a = rename a z (by swap_comm + swap_eq_rename).
    rw [swap_comm, swap_eq_rename_of_notMem_vars hzm] at h_chain
    rw [swap_comm, swap_eq_rename_of_notMem_vars hzm'] at h_chain
    exact AlphaEquiv.abs (by grind) h_chain
  | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2

/-- **Theorem 4.1** [Crole2012]: `∼p` and `∼p#` are the same relation. -/
theorem alphaEquiv_iff_alphaEquivPFresh (m n : Term Var) : m =α n ↔ AlphaEquivPFresh m n :=
  ⟨alphaEquivPFresh_of_alphaEquiv, alphaEquiv_of_alphaEquivPFresh⟩

omit [HasFresh Var] in
/-- `∼p` is contained in `∼¹p`: the side condition of `pi1` is part of that of `pi`. -/
lemma alphaEquivP1_of_alphaEquiv {m n : Term Var} (h : m =α n) : AlphaEquivP1 m n := by
  induction h with
  | var => constructor
  | abs hy _ ih => exact AlphaEquivP1.abs (by grind) ih
  | app _ _ ih1 ih2 => exact AlphaEquivP1.app ih1 ih2

/-- The case of Theorem 4.2 [Crole2012] in which the witness of `pi1` is the binder `x1` itself:
it is exchanged for an atom `z` that does not occur, using Lemmas 6.1 and 6.2(1). -/
lemma alphaEquiv_abs_of_rename_self {m1 m2 : Term Var} {x1 x2 : Var} (hx1m2 : x1 ∉ m2.vars)
    (h : m1 =α (m2.rename x2 x1)) : (Term.abs x1 m1) =α (Term.abs x2 m2) := by
  obtain ⟨z, hz⟩ : ∃ z : Var, z ∉ m1.vars ∪ m2.vars ∪ {x1, x2} :=
    Infinite.exists_notMem_finset _
  rw [← swap_eq_rename_of_notMem_vars hx1m2] at h
  have h61 := AlphaEquiv.swap_preserve (u := z) (v := x1) h
  nth_rw 3 [swap_comm] at h61
  rw [swap_comp_eq_of_notMem_vars hx1m2 (by grind), swap_comm,
    swap_eq_rename_of_notMem_vars (by grind), swap_comm,
    swap_eq_rename_of_notMem_vars (by grind)] at h61
  exact AlphaEquiv.abs (y := z) (by grind) h61

/-- `∼¹p` is contained in `∼p`: if the witness of `pi1` is one of the binders, it is exchanged
for an unused atom; otherwise it already satisfies the side condition of `pi`. -/
lemma alphaEquiv_of_alphaEquivP1 {m n : Term Var} (h : AlphaEquivP1 m n) : m =α n := by
  induction h with
  | var => constructor
  | @abs u a b E E' hy _ ih =>
    obtain rfl | hua := eq_or_ne u a
    · rw [rename_self] at ih
      exact alphaEquiv_abs_of_rename_self (by grind) ih
    obtain rfl | hub := eq_or_ne u b
    · rw [rename_self] at ih
      exact (alphaEquiv_abs_of_rename_self (by grind) ih.symm).symm
    exact AlphaEquiv.abs (y := u) (by grind) ih
  | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2

/-- **Theorem 4.2** [Crole2012]: `∼p` and `∼¹p` are the same relation. -/
theorem alphaEquiv_iff_alphaEquivP1 (m n : Term Var) : m =α n ↔ AlphaEquivP1 m n :=
  ⟨alphaEquivP1_of_alphaEquiv, alphaEquiv_of_alphaEquivP1⟩

/-- **Proposition 4.3** [Crole2012]: of the four variants of the side condition of `pi`, the
first two give `∼p` (the first is `∼p` itself, the second is Theorem 4.2), while `∼²p` and `∼³p`
relate terms with different free atoms. -/
theorem alphaEquiv_variants :
    (∀ m n : Term Var, m =α n ↔ m =α n) ∧
    (∀ m n : Term Var, AlphaEquivP1 m n ↔ m =α n) ∧
    (¬ ∀ m n : Term Var, AlphaEquivP2 m n ↔ m =α n) ∧
    (¬ ∀ m n : Term Var, AlphaEquivP3 m n ↔ m =α n) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : Var, a ≠ b :=
    ⟨fresh ∅, fresh {fresh ∅}, fun h => fresh_notMem {fresh ∅} (Finset.mem_singleton.mpr h.symm)⟩
  refine ⟨fun _ _ => Iff.rfl, fun m n => (alphaEquiv_iff_alphaEquivP1 m n).symm, ?_, ?_⟩
  · -- `λa. a z ∼²p λb. b a` with witness `z`, but `z` is free only on the left.
    obtain ⟨z, hz⟩ : ∃ z : Var, z ∉ ({a, b} : Finset Var) := Infinite.exists_notMem_finset _
    intro h
    have hP2 : AlphaEquivP2 (abs a (app (var a) (var z))) (abs b (app (var b) (var a))) := by
      refine AlphaEquivP2.abs hz (AlphaEquivP2.app ?_ ?_) <;>
        simp only [permute] <;> grind [AlphaEquivP2.var]
    have hfv := ((h _ _).mp hP2).same_fv
    simp only [fv] at hfv
    have hmem : z ∈ ({a} ∪ {z} : Finset Var) \ {a} := by grind
    rw [hfv] at hmem
    grind
  · -- `λa. b a ∼³p λb. a b` with witness `b`, but the free atoms are `b` and `a`.
    intro h
    have hP3 : AlphaEquivP3 (abs a (app (var b) (var a))) (abs b (app (var a) (var b))) := by
      refine AlphaEquivP3.abs (z := b) (AlphaEquivP3.app ?_ ?_) <;>
        simp only [permute] <;> grind [AlphaEquivP3.var]
    have hfv := ((h _ _).mp hP3).same_fv
    simp only [fv] at hfv
    have hmem : b ∈ ({b} ∪ {a} : Finset Var) \ {a} := by grind
    rw [hfv] at hmem
    grind

/-- `∼r` is contained in `∼p`: `∼p` is an equivalence and a congruence, and closed under the rule
`α` by the case `n = 1` of Lemma 6.5. Crole proves the rule `α` by an induction on the term
instead, which does not carry over to `α#`. -/
lemma alphaEquiv_of_alphaEquivR {m n : Term Var} (h : AlphaEquivR m n) : m =α n := by
  induction h with
  | refl => exact AlphaEquiv.refl _
  | symm _ ih => exact ih.symm
  | abs_congr _ ih => exact AlphaEquiv.abs_congr ih
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2
  | @alpha x x' m hx' =>
    obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m.vars ∪ (m.subst x (var x')).vars ∪ {x, x'})
    apply AlphaEquiv.abs (y := z) (by grind)
    rw [← swap_eq_rename_of_notMem_vars (m := m) (x := x) (by grind),
      ← swap_eq_rename_of_notMem_vars (m := m.subst x (var x')) (x := x') (by grind),
      swap_comm (m := m), swap_comm (m := m.subst x (var x'))]
    exact alphaEquiv_swap_subst_var (by grind) (by grind) (by grind)
      (by grind [vars_eq_fv_union_bv])

/-- `∼p` is contained in `∼r`: the rule `pi` is simulated by two instances of `α`, with
Lemma 6.3 relating the swapped bodies to the substituted ones. -/
lemma alphaEquivR_of_alphaEquiv {m n : Term Var} (h : m =α n) : AlphaEquivR m n := by
  induction h with
  | var => exact AlphaEquivR.refl
  | app _ _ ih1 ih2 => exact AlphaEquivR.app ih1 ih2
  | @abs z x1 x2 m1 m2 hz _ ih =>
    have hz1 : z ∉ m1.vars := by grind
    have hz2 : z ∉ m2.vars := by grind
    rw [← swap_eq_rename_of_notMem_vars hz1, ← swap_eq_rename_of_notMem_vars hz2,
      swap_comm (m := m1), swap_comm (m := m2)] at ih
    have hbodies : AlphaEquivR (m1.subst x1 (var z)) (m2.subst x2 (var z)) :=
      ((alphaEquivR_swap_subst_var hz1).symm.trans ih).trans (alphaEquivR_swap_subst_var hz2)
    exact ((AlphaEquivR.alpha (by grind)).trans (AlphaEquivR.abs_congr hbodies)).trans
      (AlphaEquivR.alpha (by grind)).symm

/-- **Theorem 4.4** [Crole2012]: `∼p` and `∼r` are the same relation. -/
theorem alphaEquiv_iff_alphaEquivR (m n : Term Var) : m =α n ↔ AlphaEquivR m n :=
  ⟨alphaEquivR_of_alphaEquiv, alphaEquiv_of_alphaEquivR⟩

/-- `∼r#` is contained in `∼p`: as for `∼r`, since the case `n = 1` of Lemma 6.5 needs only
freshness. -/
lemma alphaEquiv_of_alphaEquivRFresh {m n : Term Var} (h : AlphaEquivRFresh m n) : m =α n := by
  induction h with
  | refl => exact AlphaEquiv.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2
  | abs_congr _ ih => exact AlphaEquiv.abs_congr ih
  | @alpha x x' m hx' =>
    obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m.vars ∪ (m[x := var x']).vars ∪ {x, x'})
    apply AlphaEquiv.abs (y := z) (by grind)
    rw [← swap_eq_rename_of_notMem_vars (m := m) (x := x) (by grind),
      ← swap_eq_rename_of_notMem_vars (m := m.subst x (var x')) (x := x') (by grind),
      swap_comm (m := m), swap_comm (m := m.subst x (var x'))]
    exact alphaEquiv_swap_subst_var (by grind) (by grind) (by grind) (by grind)

/-- `∼p` is contained in `∼r#`: as for `∼r`, with Lemma 6.4 in place of Lemma 6.3 and `α#` in
place of `α`, which applies because non-occurrence implies freshness. -/
lemma alphaEquivRFresh_of_alphaEquiv {m n : Term Var} (h : m =α n) : AlphaEquivRFresh m n := by
  induction h with
  | var => exact AlphaEquivRFresh.refl
  | app _ _ ih1 ih2 => exact AlphaEquivRFresh.app ih1 ih2
  | @abs z x1 x2 m1 m2 hz _ ih =>
    have hz1 : z ∉ m1.vars := by grind
    have hz2 : z ∉ m2.vars := by grind
    rw [← swap_eq_rename_of_notMem_vars hz1, ← swap_eq_rename_of_notMem_vars hz2,
      swap_comm (m := m1), swap_comm (m := m2)] at ih
    have hbodies : AlphaEquivRFresh (m1.subst x1 (var z)) (m2.subst x2 (var z)) :=
      ((alphaEquivRFresh_swap_subst_var hz1).symm.trans ih).trans
        (alphaEquivRFresh_swap_subst_var hz2)
    exact ((AlphaEquivRFresh.alpha (by grind [vars_eq_fv_union_bv])).trans
      (AlphaEquivRFresh.abs_congr hbodies)).trans
        (AlphaEquivRFresh.alpha (by grind [vars_eq_fv_union_bv])).symm

/-- **Theorem 4.5** [Crole2012]: `∼p` and `∼r#` are the same relation. -/
theorem alphaEquiv_iff_alphaEquivRFresh (m n : Term Var) : m =α n ↔ AlphaEquivRFresh m n :=
  ⟨alphaEquivRFresh_of_alphaEquiv, alphaEquiv_of_alphaEquivRFresh⟩

/-- **Theorem 4.6** [Crole2012]: `∼r` and `∼r#` are the same relation, by Theorems 4.4 and 4.5. -/
theorem alphaEquivR_iff_alphaEquivRFresh (m n : Term Var) :
    AlphaEquivR m n ↔ AlphaEquivRFresh m n :=
  (alphaEquiv_iff_alphaEquivR m n).symm.trans (alphaEquiv_iff_alphaEquivRFresh m n)

/-- Theorem 4.6 [Crole2012] by Crole's direct proof, which uses renaming alone and needs his
Lemma 6.7 (substitution respects `∼r`). The statement is `alphaEquivR_iff_alphaEquivRFresh`;
what is wanted is the proof that avoids the swapping relations. -/
theorem_wanted alphaEquivR_iff_alphaEquivRFresh_direct (m n : Term Var) :
    AlphaEquivR m n ↔ AlphaEquivRFresh m n

end LambdaCalculus.Named.Untyped.Term

end Cslib
