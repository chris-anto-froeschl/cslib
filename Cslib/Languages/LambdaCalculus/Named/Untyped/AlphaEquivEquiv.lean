/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties
public import Cslib.Languages.LambdaCalculus.Named.Untyped.SwapProperties
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivLemmas

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
    -- Using Lemma 6.1
    have h61 := AlphaEquiv.swap_preserve (u := z) (v := x1) ih
    -- From Lemma 6.2 part 1
    nth_rw 3 [swap_comm] at h61
    rw [swap_comp_eq_of_not_mem_vars hx1m2 (by aesop)] at h61
    rw [swap_comm, swap_eq_rename_of_not_mem_vars (by aesop)] at h61
    rw [swap_comm, swap_eq_rename_of_not_mem_vars (by aesop)] at h61
    apply AlphaEquiv.abs (y := z) (by aesop) h61

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

/-- **Proposition 4.3** [Crole2012].  Of the four variants in the paper's table, the first
relation is `AlphaEquiv` itself and the second coincides with it by Theorem 4.2, whereas
`∼²p` and `∼³p` do not coincide with α-equivalence. -/
theorem alphaEquiv_variants :
  (∀ m n : Term Var, AlphaEquiv m n ↔ AlphaEquiv m n) ∧
  (∀ m n : Term Var, AlphaEquivP1 m n ↔ AlphaEquiv m n) ∧
  (¬ ∀ m n : Term Var, AlphaEquivP2 m n ↔ AlphaEquiv m n) ∧
  (¬ ∀ m n : Term Var, AlphaEquivP3 m n ↔ AlphaEquiv m n) := by
    and_intros
    · intro m n
      exact Iff.rfl
    · intro m n
      exact (alphaEquiv_iff_alphaEquivP1 m n).symm
    -- TODO cleanup those cases more
    · let a := HasFresh.fresh ({} : Finset Var)
      let b := HasFresh.fresh {a}
      have hab : a ≠ b := by grind [fresh_notMem]
      obtain ⟨z, hz⟩ : ∃ z : Var, z ∉ ({a, b} : Finset Var) := Infinite.exists_notMem_finset {a, b}
      have ⟨hza, hzb⟩ : z ≠ a ∧ z ≠ b := by simpa using hz
      apply not_forall.mpr
      use (abs a (app (var a) (var z)))
      apply not_forall.mpr
      use (abs b (app (var b) (var a)))
      rw [iff_comm, not_iff]
      constructor
      · intro _
        have h :
          (((var a).app (var z)).swap z a).AlphaEquivP2 (((var b).app (var a)).swap z b) := by
            apply AlphaEquivP2.app
            · simp [permute, AlphaEquivP2.var]
            · have h' : Equiv.swap z b a = a := by grind
              simp [permute, AlphaEquivP2.var, h']
        apply AlphaEquivP2.abs hz h
      · intro h h'
        -- clearly not α-equivalent: compare free variables.
        have z_h : z ∈ (abs a (app (var a) (var z))).fv := by simp [fv, hza]
        rw [h'.same_fv] at z_h
        simp [fv, hza, hzb] at z_h
    · let a := HasFresh.fresh (∅ : Finset Var)
      let b := HasFresh.fresh {a}
      have hab : a ≠ b := by grind [fresh_notMem]
      apply not_forall.mpr
      use (abs a (app (var b) (var a)))
      apply not_forall.mpr
      use (abs b (app (var a) (var b)))
      rw [iff_comm, not_iff]
      constructor
      · intro h
        apply AlphaEquivP3.abs (z := b)
        apply AlphaEquivP3.app <;> simp_all [permute, AlphaEquivP3.var]
      · intro _ h'
        -- Again, the displayed terms have different sets of free variables when `a ≠ b`.
        have b_h : b ∈ (abs a (app (var b) (var a))).fv := by simp [fv, Ne.symm hab]
        rw [h'.same_fv] at b_h
        simp [fv, hab, Ne.symm hab] at b_h

lemma alphaEquiv_of_alphaEquivR {m n : Term Var} : AlphaEquivR m n → AlphaEquiv m n := by
  intro h
  induction h with
  | refl => exact AlphaEquiv.refl _
  | symm _ ih => exact ih.symm
  | abs_congr _ ih => exact AlphaEquiv.abs_congr ih
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2
  | alpha hx' =>
    rename_i x x' m
    have hxx' : x ≠ x' := by grind
    obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m.vars ∪ (m.subst x (var x')).vars ∪ {x, x'})
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    apply AlphaEquiv.abs (y := z) (by simp_all)
    -- Bring in form of induction result by replacing `rename`s with `swap`s
    rw [← swap_eq_rename_of_not_mem_vars (m := m) (x := x) (by simp_all)]
    rw [← swap_eq_rename_of_not_mem_vars (m := m.subst x (var x')) (x := x') (by simp_all)]
    rw [swap_comm (m := m), swap_comm (m := m.subst x (var x'))]
    -- Induction result statement already provided by special case of lemma 6.5
    exact alphaEquiv_swap_subst_var
      (by simp_all) (by simp_all) hxx' (by simp_all [vars_either_fv_or_bv])

lemma alphaEquivR_of_alphaEquiv {m n : Term Var} : AlphaEquiv m n → AlphaEquivR m n := by
  intro h
  induction h with
  | var => exact AlphaEquivR.refl
  | app _ _ ih1 ih2 => exact AlphaEquivR.app ih1 ih2
  | @abs z x1 x2 m1 m2 hz hbody ih =>
    have hz1 : z ∉ m1.vars := by simp_all
    have hz2 : z ∉ m2.vars := by simp_all
    -- The induction hypothesis in the paper's swap form `(z a) · E ∼r (z b) · E'`.
    rw [← swap_eq_rename_of_not_mem_vars hz1, ← swap_eq_rename_of_not_mem_vars hz2] at ih
    rw [swap_comm (m := m1), swap_comm (m := m2)] at ih
    -- Lemma 6.3, twice, together with `trans`.
    have hbodies : AlphaEquivR (m1.subst x1 (var z)) (m2.subst x2 (var z)) :=
      ((alphaEquivR_swap_subst_var hz1).symm.trans ih).trans (alphaEquivR_swap_subst_var hz2)
    -- Using `bcg`
    have hbsubstar: AlphaEquivR (abs z (m1.subst x1 (var z))) (abs z (m2.subst x2 (var z))) :=
      AlphaEquivR.abs_congr hbodies
    -- then the two instances of `α`,
    have hbazsubst: AlphaEquivR (abs x1 m1) (abs z (m1.subst x1 (var z))) :=
      AlphaEquivR.alpha (by simp_all)
    have hbbzsubst: AlphaEquivR (abs x2 m2) (abs z (m2.subst x2 (var z))) :=
      AlphaEquivR.alpha (by simp_all)
    -- and `sym`, `trans`.
    apply AlphaEquivR.symm at hbbzsubst
    apply AlphaEquivR.trans hbazsubst
    apply AlphaEquivR.trans hbsubstar
    exact hbbzsubst

/-! ## Theorem 4.4 [Crole2012] -/
theorem alphaEquiv_iff_alphaEquivR (m n : Term Var) :
    AlphaEquiv m n ↔ AlphaEquivR m n := by
  exact ⟨alphaEquivR_of_alphaEquiv, alphaEquiv_of_alphaEquivR⟩

/-- The cases are literally those of `alphaEquiv_of_alphaEquivR`, except that the rule
`α` is replaced by `α#`. -/
lemma alphaEquiv_of_alphaEquivRFresh {m n : Term Var} :
    AlphaEquivRFresh m n → AlphaEquiv m n := by
  intro h
  induction h with
  | refl => exact AlphaEquiv.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2
  | abs_congr _ ih => exact AlphaEquiv.abs_congr ih
  | alpha hx' =>
    rename_i x x' m
    have hxx' : x ≠ x' := by symm; simp_all
    have hx'fv : x' ∉ m.fv := by simp_all
    -- Pick an atom `z` occurring neither in `E` nor in `E{x'/x}`, and distinct from `x, x'`.
    obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m.vars ∪ (m[x := var x']).vars ∪ {x, x'})
    rw [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    apply AlphaEquiv.abs (y := z) (by grind)
    have hzm : z ∉ m.vars := by simp_all
    -- With `z` fresh, both renamings are swaps, and the goal is the one-variable Lemma 6.5.
    rw [← swap_eq_rename_of_not_mem_vars (m := m) (x := x) hzm]
    rw [← swap_eq_rename_of_not_mem_vars (m := m.subst x (var x')) (x := x') (by grind)]
    rw [swap_comm (m := m), swap_comm (m := m.subst x (var x'))]
    exact alphaEquiv_swap_subst_var hzm (by simp_all) hxx' hx'fv

/-- The steps are exactly those of the corresponding half of Theorem 4.4
(`alphaEquivR_of_alphaEquiv`), with Lemma 6.4 used in place of Lemma 6.3, and with the two
instances of `α` replaced by `α#`, which is legitimate because `z ̸▹ E, E'` implies `z # E, E'`. -/
lemma alphaEquivRFresh_of_alphaEquiv {m n : Term Var} :
    AlphaEquiv m n → AlphaEquivRFresh m n := by
  intro h
  induction h with
  | var => exact AlphaEquivRFresh.refl
  | app _ _ ih1 ih2 => exact AlphaEquivRFresh.app ih1 ih2
  | @abs z x1 x2 m1 m2 hz hbody ih =>
    have hz1 : z ∉ m1.vars := by simp_all
    have hz2 : z ∉ m2.vars := by simp_all
    rw [← swap_eq_rename_of_not_mem_vars hz1, ← swap_eq_rename_of_not_mem_vars hz2] at ih
    rw [swap_comm (m := m1), swap_comm (m := m2)] at ih
    -- Lemma 6.4, twice, together with `trans`.
    have hbodies : AlphaEquivRFresh (m1.subst x1 (var z)) (m2.subst x2 (var z)) :=
      ((alphaEquivRFresh_swap_subst_var hz1).symm.trans ih).trans
        (alphaEquivRFresh_swap_subst_var hz2)
    -- Using `bcg`
    have hbsubstar: AlphaEquivRFresh (abs z (m1.subst x1 (var z))) (abs z (m2.subst x2 (var z))) :=
      AlphaEquivRFresh.abs_congr hbodies
    -- then the two instances of `α`,
    have hbazsubst: AlphaEquivRFresh (abs x1 m1) (abs z (m1.subst x1 (var z))) :=
      AlphaEquivRFresh.alpha (by simp_all [vars_either_fv_or_bv])
    have hbbzsubst: AlphaEquivRFresh (abs x2 m2) (abs z (m2.subst x2 (var z))) :=
      AlphaEquivRFresh.alpha (by simp_all [vars_either_fv_or_bv])
    -- and `sym`, `trans`.
    apply AlphaEquivRFresh.symm at hbbzsubst
    apply AlphaEquivRFresh.trans hbazsubst
    apply AlphaEquivRFresh.trans hbsubstar
    exact hbbzsubst

/-! ## Theorem 4.5 [Crole2012] -/
theorem alphaEquiv_iff_alphaEquivRFresh (m n : Term Var) :
    AlphaEquiv m n ↔ AlphaEquivRFresh m n :=
  ⟨alphaEquivRFresh_of_alphaEquiv, alphaEquiv_of_alphaEquivRFresh⟩

/-- **Theorem 4.6** [Crole2012].

As the paper notes, this follows from Theorems 4.4 and 4.5. The paper's alternative direct
proof, which uses only traditional renaming techniques, is given separately below as
`alphaEquivR_iff_alphaEquivRFresh_direct`. -/
theorem alphaEquivR_iff_alphaEquivRFresh (m n : Term Var) :
    AlphaEquivR m n ↔ AlphaEquivRFresh m n :=
  (alphaEquiv_iff_alphaEquivR m n).symm.trans (alphaEquiv_iff_alphaEquivRFresh m n)

theorem alphaEquivR_iff_alphaEquivRFresh_direct (m n : Term Var) :
    AlphaEquivR m n ↔ AlphaEquivRFresh m n := sorry

end LambdaCalculus.Named.Untyped.Term

end Cslib
