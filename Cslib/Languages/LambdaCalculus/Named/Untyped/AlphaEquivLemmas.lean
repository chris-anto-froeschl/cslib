/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties
public import Cslib.Languages.LambdaCalculus.Named.Untyped.SwapProperties

/-! # The lemmas of Section 6.1 of [Crole2012]

Section 6 of [Crole2012] collects the auxiliary results that the proofs of the theorems of
Section 4 rely on.  This file formalises the lemmas of Section 6.1 (the ones about
expressions; Section 6.2 is about program contexts) which are not already available:

* **Lemma 6.1** `E ∼p E' ⟹ (u v) · E ∼p (u v) · E'` is `AlphaEquiv.swap_preserve`, proved in
  `SwapProperties.lean`.
* **Lemma 6.2** (both parts, about agreement sets of permutations) consists of
  `permute_eq_of_vars_subset_agreementSet` and
  `permute_alphaEquiv_of_fv_subset_agreementSet`, also proved in `SwapProperties.lean`.
* **Lemma 6.3** `z ̸▹ E ⟹ (z a) · E ∼r E{z/a}` is `alphaEquivR_swap_subst_var`.
* **Lemma 6.4** `z ̸▹ E ⟹ (z a) · E ∼r# E{z/a}` is `alphaEquivRFresh_swap_subst_var`.
* **Lemma 6.5** the simultaneous-renaming strengthening used for the rule `α#` in
  Theorem 4.5, is `alphaEquiv_swapChain` (with the one-variable instance
  `alphaEquiv_swap_subst_var`).
* **Lemma 6.6** `a # E ⟹ (∃Ê)(a ̸▹ Ê ∧ Ê ∼r E)` is `alphaEquivR_avoid_var`.

Lemma 6.7 (`E ∼r E' ⟹ E{a/b} ∼r E'{a/b}`) is stated and proved in `AlphaEquivEquiv.lean`,
because the proof given here goes through Theorem 4.4; see the discussion there.

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012], Section 6.1
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped.Term

/-! ## Lemma 6.3 and Lemma 6.4

Both lemmas say that swapping a completely fresh atom `z` for `a` has the same effect as
renaming `a` to `z` by capture-avoiding substitution, the first for `∼r`, the second for
`∼r#`.  The paper proves Lemma 6.3 by structural induction on `E`, the only interesting case
being a binding expression `B([b]E)` with `b = a`, where the rule `α` is used; and it obtains
Lemma 6.4 by the same induction, replacing that use of `α` by `α#` (which is legitimate,
since `z ̸▹ E` implies `z ∉ free(E)`).  Both inductions are carried out below.
-/

/-- Renaming toward a completely fresh variable agrees, up to `∼r`, with capture-avoiding
substitution of that variable.  This is the `rename`-form of the paper's **Lemma 6.3**;
`Term.swap` coincides with `Term.rename` precisely under the hypothesis `z ∉ m.vars`. -/
lemma alphaEquivR_rename_subst_var {m : Term Var} {x z : Var}
    (hz : z ∉ m.vars) :
    AlphaEquivR (m.rename x z) (m.subst x (var z)) := by
  induction m with
  | var y =>
    -- The steps for atoms are easy.
    by_cases hyx : y = x <;> simp [rename, subst, hyx, AlphaEquivR.refl]
  | app m1 m2 ih1 ih2 =>
    -- ... and so are the steps for `P(E₁, E₂)`, by `pcg`.
    simp only [rename, subst]
    apply AlphaEquivR.app
    · exact ih1 (by grind [vars])
    · exact ih2 (by grind [vars])
  | abs y m ih =>
    have hzy : z ≠ y := by grind [vars]
    by_cases hyx : y = x
    · -- (Case `a = b` of the paper): the binder itself is renamed, and the rule `α` is used.
      subst y
      simp only [rename, subst, reduceIte]
      apply AlphaEquivR.symm
      apply AlphaEquivR.trans (AlphaEquivR.alpha (x' := z) (by grind [vars]))
      apply AlphaEquivR.abs_congr
      exact (ih (by grind [vars])).symm
    · -- (Case `a ≠ b` of the paper): `z ≠ b`, so no capture, and `bcg` applies.
      have hyz : y ≠ z := Ne.symm hzy
      simp only [rename, subst, hyx, reduceIte, fv, hyz, Finset.mem_singleton, not_false_eq_true]
      apply AlphaEquivR.abs_congr
      exact ih (by grind [vars])

/-- **Lemma 6.3** [Crole2012]: `z ̸▹ E ⟹ (z a) · E ∼r E{z/a}`. -/
lemma alphaEquivR_swap_subst_var {m : Term Var} {a z : Var} (hz : z ∉ m.vars) :
    AlphaEquivR (m.swap z a) (m.subst a (var z)) := by
  rw [swap_comm, swap_eq_rename_of_not_mem_vars hz]
  exact alphaEquivR_rename_subst_var hz

/-- The `rename`-form of the paper's **Lemma 6.4**: the induction of
`alphaEquivR_rename_subst_var` with every use of the rule `α` replaced by `α#`. -/
lemma alphaEquivRFresh_rename_subst_var {m : Term Var} {x z : Var}
    (hz : z ∉ m.vars) :
    AlphaEquivRFresh (m.rename x z) (m.subst x (var z)) := by
  induction m with
  | var y =>
    by_cases hyx : y = x <;> simp [rename, subst, hyx, AlphaEquivRFresh.refl]
  | app m₁ m₂ ih₁ ih₂ =>
    simp only [rename, subst]
    apply AlphaEquivRFresh.app
    · exact ih₁ (by grind [vars])
    · exact ih₂ (by grind [vars])
  | abs y m ih =>
    have hzy : z ≠ y := by grind [vars]
    by_cases hyx : y = x
    · -- The only step of the induction that uses `α`; here `α#` is used instead, which is
      -- legitimate because `z ̸▹ E` implies `z # E`.
      subst y
      simp only [rename, subst, reduceIte]
      apply AlphaEquivRFresh.symm
      apply AlphaEquivRFresh.trans
        (AlphaEquivRFresh.alpha (x' := z) (by grind [vars, vars_either_fv_or_bv]))
      apply AlphaEquivRFresh.abs_congr
      exact (ih (by grind [vars])).symm
    · have hyz : y ≠ z := Ne.symm hzy
      simp only [rename, subst, hyx, reduceIte, fv, hyz, Finset.mem_singleton, not_false_eq_true]
      apply AlphaEquivRFresh.abs_congr
      exact ih (by grind [vars])

/-- **Lemma 6.4** [Crole2012]: `z ̸▹ E ⟹ (z a) · E ∼r# E{z/a}`. -/
lemma alphaEquivRFresh_swap_subst_var {m : Term Var} {a z : Var} (hz : z ∉ m.vars) :
    AlphaEquivRFresh (m.swap z a) (m.subst a (var z)) := by
  rw [swap_comm, swap_eq_rename_of_not_mem_vars hz]
  exact alphaEquivRFresh_rename_subst_var hz

end LambdaCalculus.Named.Untyped.Term

end Cslib
