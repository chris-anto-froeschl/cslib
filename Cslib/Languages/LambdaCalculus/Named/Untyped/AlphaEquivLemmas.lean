/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties
public import Cslib.Languages.LambdaCalculus.Named.Untyped.SwapProperties

/-! # The lemmas of Section 6.1 of [Crole2012]

This file formalises the expression lemmas of Section 6.1.

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012], Section 6.1
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped.Term

/-- Lemma 6.1 [Crole2012]: Swap (transposition) preserves α-equivalence. -/
lemma AlphaEquiv.swap_preserve {m m' : Term Var} {u v : Var} :
  m =α m' → (m.swap u v) =α (m'.swap u v) := by
    intro h1
    by_cases h2 : u = v
    · simp_all
    · change u ≠ v at h2
      induction h1 with
      | var => simp_all [AlphaEquiv.refl]
      | abs hm1 hm2 ih =>
        rename_i z a b E E'
        have z_h1 : z ≠ a := by simp_all
        have z_h2 : z ≠ b := by simp_all
        have h3 : a = u ∨ a = v ∨ (a ≠ u ∧ a ≠ v) := by grind
        have h4 : b = u ∨ b = v ∨ (b ≠ u ∧ b ≠ v) := by grind
        have h5 : z = u ∨ z = v ∨ (z ≠ u ∧ z ≠ v) := by grind
        -- we've got 27 cases to consider
        rcases h3 with ha | ha | ⟨hau, hav⟩
        · rcases h4 with hb | hb | ⟨hbu, hbv⟩
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            · simp_all
            -- representative example 4 case of: a = u; b = u; z = v
            · subst ha; subst hb; subst hz
              exact alphaEquiv_swap_preserve_abs_a_eq_b_eq_u (by simp_all) ih h2
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            · simp_all
            · simp_all
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            · simp_all
            -- example 3 reuse
            · subst ha; subst hz
              apply AlphaEquiv.symm
              exact (alphaEquiv_swap_preserve_abs_b_eq_u (by grind) (AlphaEquiv.symm ih) hbu hbv h2)
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
        · rcases h4 with hb | hb | ⟨hbu, hbv⟩
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            · simp_all
            · simp_all
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            -- example 4 reuse
            · subst ha; subst hb; subst hz
              nth_rw 1 [swap_comm]
              nth_rw 2 [swap_comm]
              symm at z_h2
              nth_rw 1 [swap_comm] at ih
              nth_rw 2 [swap_comm] at ih
              apply alphaEquiv_swap_preserve_abs_a_eq_b_eq_u (by simp_all) ih z_h2
            · simp_all
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            -- example 3 reuse
            · subst ha; subst hz
              nth_rw 1 [swap_comm]
              nth_rw 2 [swap_comm]
              apply AlphaEquiv.symm
              symm at h2
              apply alphaEquiv_swap_preserve_abs_b_eq_u (by simp_all) _ hbv hbu h2
              apply AlphaEquiv.symm
              nth_rw 1 [swap_comm]
              nth_rw 2 [swap_comm]
              exact ih
            · simp_all
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
        · rcases h4 with hb | hb | ⟨hbu, hbv⟩
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            · simp_all
            -- representative example 3 case of: a ≠ u, v; b = u; z = v
            · subst hb; subst hz
              exact alphaEquiv_swap_preserve_abs_b_eq_u (by simp_all) ih hau hav h2
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            -- example 3 reuse
            · subst hb; subst hz
              nth_rw 1 [swap_comm]
              nth_rw 2 [swap_comm]
              symm at h2
              apply alphaEquiv_swap_preserve_abs_b_eq_u (by simp_all) _ hav hau h2
              nth_rw 1 [swap_comm]
              nth_rw 2 [swap_comm]
              exact ih
            · simp_all
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            -- representative example 2 case of: a ≠ u, v; b ≠ u, v; z = u
            -- use z' = v
            · subst hz
              exact alphaEquiv_swap_preserve_abs_fresh_z_eq_u hm1 ih hau hav hbu hbv
            -- example 2 reuse after adjusting via swap commutativity and choosing z' = u
            · rw [swap_comm (m := Term.abs a E) (x := u) (y := v),
                  swap_comm (m := Term.abs b E') (x := u) (y := v)]
              subst hz
              nth_rw 1 [swap_comm] at ih
              nth_rw 2 [swap_comm] at ih
              exact alphaEquiv_swap_preserve_abs_fresh_z_eq_u hm1 ih hav hau hbv hbu
            -- representative example 1 case of: z ≠ u, v
            -- use z' = z
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
      | app hm1 hm2 ih1 ih2 => exact AlphaEquiv.app ih1 ih2

omit [HasFresh Var] in
/-- Lemma 6.2 part 1 [Crole2012]: Permutations on agreement set result in same term. -/
lemma permute_eq_of_vars_subset_agreementSet (m : Term Var) (π π' : Equiv.Perm Var)
  (h : (m.vars : Set Var) ⊆ agreementSet π π') :
  m.permute π = m.permute π' := by
    induction m with
    | var x => simp_all [permute, vars, agreementSet, vars]
    | abs x m ih =>
      have hx : π x = π' x := h (by simp [vars])
      have hm : m.permute π = m.permute π' := ih fun y hy => h (by simp [vars, hy])
      simp [permute, hx, hm]
    | app m n ihm ihn =>
      have hm : m.permute π = m.permute π' := ihm fun y hy => h (by simp [vars, hy])
      have hn : n.permute π = n.permute π' := ihn fun y hy => h (by simp [vars, hy])
      simp [permute, hm, hn]

omit [HasFresh Var] in
/-- Lemma 6.2 part 1 [Crole2012] (specialized): Swaps on non occuring variables result in same
term -/
lemma swap_comp_eq_of_not_mem_vars {m : Term Var} {a u z : Var}
  (hu : u ∉ m.vars) (hz : z ∉ m.vars) :
  (m.swap u a).swap z u = m.swap z a := by
    unfold swap
    let π :=  (Equiv.swap z u) * (Equiv.swap u a)
    let π' := Equiv.swap z a
    have h : (m.vars : Set Var) ⊆ agreementSet π π' := by
      intro x hx
      simp only [agreementSet, Set.mem_setOf_eq, π, π', Equiv.Perm.coe_mul, Function.comp_apply]
      grind
    rw [permute_permute m (Equiv.swap u a) (Equiv.swap z u)]
    exact permute_eq_of_vars_subset_agreementSet m π π' h

/-- Lemma 6.2 part 2 [Crole2012]: Same as 6.1 but wrt free variables and alpha equivalence. -/
lemma permute_alphaEquiv_of_fv_subset_agreementSet (m : Term Var) (π π' : Equiv.Perm Var)
  (h : (m.fv : Set Var) ⊆ agreementSet π π') :
  (m.permute π) =α (m.permute π') := by
    induction m generalizing π π' with
    | var x =>
      unfold permute
      have hx : π x = π' x := by
        unfold agreementSet at h
        apply h
        unfold fv
        rw [Finset.coe_singleton, Set.mem_singleton_iff]
      rw [hx]
      exact AlphaEquiv.var
    | app m n ihm ihn =>
      have hm : (m.permute π) =α (m.permute π') := by
        apply ihm
        intro x hx
        apply h
        unfold fv
        simp_all
      have hn : (n.permute π) =α (n.permute π') := by
        apply ihn
        intro x hx
        apply h
        unfold fv
        simp_all
      apply AlphaEquiv.app hm hn
    | abs a m ih =>
      let z := HasFresh.fresh ((m.permute π).vars ∪ (m.permute π').vars ∪ {π a, π' a})
      have hz := HasFresh.fresh_notMem ((m.permute π).vars ∪ (m.permute π').vars ∪ {π a, π' a})
      have hzπ : z ∉ (m.permute π).vars := by simp_all [z]
      have hzπ' : z ∉ (m.permute π').vars := by simp_all [z]
      have hbody :
        (m.permute (π.trans (Equiv.swap (π a) z))) =α (m.permute (π'.trans (Equiv.swap (π' a) z)))
        := by
          apply ih
          intro x hx
          simp only [agreementSet, Set.mem_setOf_eq, Equiv.trans_apply]
          by_cases hxa : x = a
          · simp_all
          · have hagree : π x = π' x := h (by simp [fv, hx, hxa])
            have hπxa : π x ≠ π a := fun he => hxa (π.injective he)
            have hπ'xa : π' x ≠ π' a := fun he => hxa (π'.injective he)
            have hπ'xπa : π' x ≠ π a := by simp_all
            have hπxz : π x ≠ z := by
              intro he
              apply hzπ
              rw [← he, vars_either_fv_or_bv]
              apply Finset.mem_union_left
              rw [permute_fv]
              exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
            have hπ'xz : π' x ≠ z := by simp_all
            simp [Equiv.swap_apply_def, hπ'xa, hπ'xπa, hπ'xz, hagree]
      rw [← permute_trans, ← permute_trans, permute_swap, permute_swap] at hbody
      rw [swap_eq_rename_of_not_mem_vars hzπ, swap_eq_rename_of_not_mem_vars hzπ'] at hbody
      unfold permute
      apply AlphaEquiv.abs (y := z) (by simp_all [z]) hbody

/-- Lemma 6.2 part 2 [Crole2012] (specialized). -/
lemma swap_comp_alphaEquiv_of_not_mem_fv {m : Term Var} {a u z : Var}
  (hu : u ∉ m.fv) (hz : z ∉ m.fv) :
  ((m.swap u a).swap z u) =α (m.swap z a) := by
    let π := (Equiv.swap u a).trans (Equiv.swap z u)
    let π' := Equiv.swap z a
    have h : (m.fv : Set Var) ⊆ agreementSet π π' := by
      intro x hx
      unfold agreementSet
      rw [Set.mem_setOf_eq]
      grind
    have h' := permute_alphaEquiv_of_fv_subset_agreementSet m π π' h
    rw [← permute_trans, permute_swap, permute_swap, permute_swap] at h'
    exact h'

/-- Renaming toward a completely fresh variable agrees, up to `∼r`, with capture-avoiding
substitution of that variable.

This is the `rename`-form of the paper's Lemma 6.3. -/
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

/-- Lemma 6.3 [Crole2012]: `z ̸▹ E ⟹ (z a) · E ∼r E{z/a}`. -/
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
  | app m1 m1 ih1 ih2 =>
    simp only [rename, subst]
    apply AlphaEquivRFresh.app
    · exact ih1 (by grind [vars])
    · exact ih2 (by grind [vars])
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

/-- Lemma 6.4 [Crole2012]: `z ̸▹ E ⟹ (z a) · E ∼r# E{z/a}`. -/
lemma alphaEquivRFresh_swap_subst_var {m : Term Var} {a z : Var} (hz : z ∉ m.vars) :
    AlphaEquivRFresh (m.swap z a) (m.subst a (var z)) := by
  rw [swap_comm, swap_eq_rename_of_not_mem_vars hz]
  exact alphaEquivRFresh_rename_subst_var hz

/-- Lemma 6.6 [Crole2012]: We can always re-name bound atoms so that a particular atom does not
occur. -/
lemma alphaEquivR_avoid_var {m : Term Var} {a : Var} (ha : a ∉ m.fv) :
    ∃ m', a ∉ m'.vars ∧ AlphaEquivR m' m := by
  induction m with
  | var y => exact ⟨var y, by grind [vars, fv], AlphaEquivR.refl⟩
  | app m1 m2 ih1 ih2 =>
    obtain ⟨n1, hn1, he1⟩ := ih1 (by grind [fv])
    obtain ⟨n2, hn2, he2⟩ := ih2 (by grind [fv])
    exact ⟨app n1 n2, by grind [vars], AlphaEquivR.app he1 he2⟩
  | abs y E ih =>
    by_cases hay : a = y
    · -- The paper's case `a = b`: pick `z ̸▹ a, E` and use `B([a]E) ∼r B([z]E{z/a})`.
      -- Renaming the binder `a` also renames every occurrence of `a` in the body, so a
      -- single step suffices and no appeal to the induction hypothesis is needed.
      subst hay
      obtain ⟨z, hz⟩ := HasFresh.fresh_exists (E.vars ∪ {a})
      have hzE : z ∉ E.vars := by grind
      have haz : a ≠ z := by grind
      use abs z (E.rename a z)
      split_ands
      · have hanin := rename_remove (m := E) (x := a) (y := z) haz
        grind [vars]
      · have halpha : AlphaEquivR (abs a E) (abs z (E.subst a (var z))) :=
          AlphaEquivR.alpha (by grind)
        have hren : AlphaEquivR (E.rename a z) (E.subst a (var z)) :=
          alphaEquivR_rename_subst_var hzE
        exact (AlphaEquivR.abs_congr hren).trans halpha.symm
    · -- The paper's case `a ̸▹ free(E)`, which "is easy": the induction hypothesis applies.
      obtain ⟨E', hE', he⟩ := ih (by grind [fv])
      exact ⟨abs y E', by grind [vars], AlphaEquivR.abs_congr he⟩

end LambdaCalculus.Named.Untyped.Term

end Cslib
