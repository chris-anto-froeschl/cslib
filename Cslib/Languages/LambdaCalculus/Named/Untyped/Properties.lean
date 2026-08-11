/-
Copyright (c) 2026 Haoxuan Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoxuan Yin, Fabrizio Montesi
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivDefs

/-! # Properties of λ-calculus terms and α-equivalence

Basic properties of renaming, variable sets, and α-equivalence.

The reflexivity, symmetry, and transitivity of `AlphaEquiv` (`∼p`, Definition 3.1)
follow from Theorem 4.4 in [Crole2012], which establishes that `∼p` coincides with
`∼r` (Definition 3.4), the latter being defined as an equivalence relation.
Here they are proved directly for `∼p` by structural/well-founded induction.

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012]
-/

public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.Named.Untyped.Term

/-- A variable in a term is either free or bound. -/
theorem vars_either_fv_or_bv {m : Term Var} :
    m.vars = m.fv ∪ m.bv := by
  induction m <;> grind [fv, bv, vars]

/-- Renaming an unused variable has no effect. -/
@[simp]
theorem rename_unused {m : Term Var} {x y : Var} :
  x ∉ m.vars → m.rename x y = m := by
  induction m <;> grind [vars, rename]

/-- Renaming a variable to itself has no effect. -/
@[simp]
theorem rename_same {m : Term Var} {x : Var} :
  m.rename x x = m := by
  induction m <;> grind [vars, rename]

/-- Renaming a used variable changes the set of variables. -/
@[simp]
theorem rename_vars_used {m : Term Var} {x y : Var} :
  x ∈ m.vars → (m.rename x y).vars = m.vars.erase x ∪ {y} := by
  induction m with
  | var z => grind [vars, rename]
  | abs z m ih =>
    intro hx
    by_cases hxm : x ∈ m.vars <;> grind [vars, rename, rename_unused]
  | app m n ihm ihn =>
    intro hx
    by_cases hxm : x ∈ m.vars
    · by_cases hxn : x ∈ n.vars <;> grind [vars, rename, rename_unused]
    · have hxn : x ∈ n.vars := by grind [vars]
      grind [vars, rename, rename_unused]

/-- Renaming removes the variable. -/
theorem rename_remove {m : Term Var} {x y : Var} :
  x ≠ y → x ∉ (m.rename x y).vars := by
  intro hxy
  by_cases hx : x ∈ m.vars <;> grind [rename_vars_used, rename_unused]

/-- The set of variables after renaming. -/
theorem rename_vars {m : Term Var} {x y : Var} :
  (m.rename x y).vars = m.vars \ {x} ∪ (if x ∈ m.vars then {y} else ∅) := by
  by_cases x ∈ m.vars <;> grind [vars, rename, rename_unused, rename_vars_used]

/-- The set of free variables after renaming. -/
theorem rename_fv {m : Term Var} {x y : Var} :
  y ∉ m.vars → (m.rename x y).fv = m.fv \ {x} ∪ (if x ∈ m.fv then {y} else ∅) := by
  induction m <;> grind [fv, vars, rename, vars_either_fv_or_bv]

/-- Concatenation of renaming. -/
@[simp]
theorem rename_concat {m : Term Var} {x y z : Var} :
  y ∉ m.vars → (m.rename x y).rename y z = m.rename x z := by
  induction m <;> grind [vars, rename]

/-- Commutativity of renaming, simpler version. -/
theorem rename_comm {m : Term Var} {x y z w : Var} :
  x ≠ z → y ∉ m.vars ∪ {x, z} → w ∉ m.vars ∪ {x, z} →
  (m.rename x y).rename z w = (m.rename z w).rename x y := by
  induction m <;> grind [vars, rename]

/-- Commutativity of renaming, more general version. -/
theorem rename_comm2 {m : Term Var} {x y z w : Var} :
    y ∉ m.vars ∪ {x, z} → w ∉ m.vars ∪ {x, y, z} →
    (m.rename x y).rename (if z = x then y else z) w = (m.rename z w).rename x y := by
  intro hy hw
  by_cases hzx : z = x
  · grind [rename_same, rename_unused, rename_concat, rename_vars]
  · grind [rename_comm]

omit [DecidableEq Var] in
@[grind norm↓← ]
lemma induction_by_sizeOf {m n : Term Var} : sizeOf m < sizeOf n ↔ WellFoundedRelation.rel m n := by
  rfl

/-- α-equivalent terms have the same size. -/
theorem AlphaEquiv.eq_sizeOf {m n : Term Var} : m =α n → sizeOf m = sizeOf n := by
  intro h
  induction h with
  | @var x => rfl
  | @abs y x1 x2 m1 m2 hy h ih =>
    simpa using ih
  | @app m1 n1 m2 n2 _ hm hn =>
    grind

/-- α-equivalent terms have the same free variables. -/
theorem AlphaEquiv.same_fv {m n : Term Var} : m =α n → m.fv = n.fv := by
  intro h
  induction h with
  | @var x => rfl
  | @abs y x1 x2 m1 m2 hy h ih =>
    rw [Term.fv, Term.fv]
    have h1 : m1.fv \ {x1} = (m1.rename x1 y).fv \ {y} := by
      grind [rename_fv, vars_either_fv_or_bv]
    have h2 : (m2.rename x2 y).fv \ {y} = m2.fv \ {x2} := by
      grind [rename_fv, vars_either_fv_or_bv]
    grind
  | @app m1 n1 m2 n2 h1 h2 ih1 ih2 => grind [Term.fv]

@[simp]
lemma swap_self {m : Term Var} {x : Var} : m.swap x x = m := by
  induction m <;> simp_all [swap, permute]

lemma swap_comm {m : Term Var} {x y : Var} : m.swap x y = m.swap y x := by
  unfold swap
  rw [Equiv.swap_comm]

@[simp]
lemma swap_involutive {m : Term Var} {x y : Var} : (m.swap x y).swap x y = m := by
  induction m <;> simp_all [swap, permute]

@[simp]
lemma swap_preserves_sizeOf {m : Term Var} {x y : Var} : sizeOf (m.swap x y) = sizeOf m := by
  induction m <;> simp_all [swap, permute]

@[simp]
lemma swap_unused {m : Term Var} {x y : Var} : x ∉ m.vars → y ∉ m.vars → m.swap x y = m := by
  induction m <;> grind [swap, permute, vars]

/-- When `y ∉ m.vars`, `swap x y` and `rename x y` coincide.

This is because `rename x y` only changes `x` to `y` (not `y` to `x`), and when `y` does
not occur in `m`, swapping and renaming produce the same result. -/
lemma swap_eq_rename_of_not_mem_vars {m : Term Var} {x y : Var}
  (hy : y ∉ m.vars) : m.swap x y = m.rename x y := by
    induction m with
    | var z =>
      unfold swap rename
      grind [Term.vars, permute]
    | abs z m ih =>
      simp_all [Term.swap, Term.rename, Term.vars, permute]
      grind
    | app n1 n2 ih1 ih2 =>
      simp_all [Term.swap, Term.rename, Term.vars, permute]

/-- The set of free variables after a swap. -/
lemma swap_fv {m : Term Var} {x y : Var} :
    (m.swap x y).fv = m.fv.image fun z => if z = x then y else if z = y then x else z := by
      induction m with
      | var z => aesop
      | abs z m ih =>
        simp_all [Term.swap, Term.fv, Finset.ext_iff, Finset.mem_image, Finset.mem_sdiff, permute]
        grind
      | app m n ih1 ih2 =>
        simp_all only [Term.swap, Term.fv, permute]
        rw [Finset.image_union]

/-- Swapping preserves non-membership in `fv`. -/
lemma fresh_swap {m : Term Var} {x y z : Var} (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.fv) :
  z ∉ (m.swap x y).fv := by
    rw [swap_fv]
    grind

/-- The set of vars after a swap. -/
lemma swap_vars {m : Term Var} {x y z : Var} (hzm : z ∉ m.vars) :
  (m.swap x y).vars = m.vars.image fun z => if z = x then y else if z = y then x else z := by
    induction m with
    | var w => aesop
    | abs w m ih => simp_all [Term.swap, Term.vars, permute]; grind
    | app m n ih1 ih2 =>
      simp_all only [Term.swap, Term.vars, Finset.image_union, permute]
      grind

/-- Swapping preserves non-membership in `vars`. -/
lemma not_mem_vars_swap {m : Term Var} {x y z : Var}
  (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.vars) : z ∉ (m.swap x y).vars := by
    rw [swap_vars hzm]
    grind

/-- `swap` and `rename` commute (modulo the permutation action on the variable arguments). -/
lemma swap_rename_comm {m : Term Var} {u v x y : Var} :
  (m.swap u v).rename (Equiv.swap u v x) (Equiv.swap u v y) = (m.rename x y).swap u v := by
    induction m with
    | var z =>
      simp_all [Term.swap, Term.rename, permute]
      grind
    | abs z m ih =>
      simp_all [Term.swap, Term.rename, permute]
      grind
    | app m n ih1 ih2 =>
      simp_all [Term.swap, Term.rename, permute]

lemma swap_rename_comm' {m : Term Var} {u v x z : Var} (hzu : z ≠ u) (hzv : z ≠ v) :
  (m.swap u v).rename (Equiv.swap u v x) z = (m.rename x z).swap u v := by
    rw [← @swap_rename_comm _ _ m u v x z]
    simp_all
    grind

/-- Term-level conjugation identity: `(m.swap u v).swap v a = (m.swap u a).swap u v`
when `a ∉ {u, v}`.

Unlike `swap_comp_eq_of_not_mem_vars`, this holds unconditionally (no freshness needed). -/
lemma swap_comp_eq_of_ne {m : Term Var} {a u v : Var} (hau : a ≠ u) (hav : a ≠ v) :
  (m.swap u v).swap v a = (m.swap u a).swap u v := by
    induction m with
    | var x => simp_all [Term.swap, permute]; grind
    | app m n ihm ihn => simp_all [Term.swap, permute]
    | abs x m ih => simp_all [Term.swap, permute]; grind

/-- If `u` is not among `m`'s variables, then `v` cannot appear in `m.swap u v`
(the only way `v` could show up is as the image of `u`). -/
lemma not_mem_swap_target {m : Term Var} {u v : Var} (hu : u ∉ m.vars) : v ∉ (m.swap u v).vars := by
  rw [swap_vars hu]
  grind

/-- Permuting a term transports its free variables pointwise. -/
lemma permute_fv (m : Term Var) (π : Equiv.Perm Var) :
  (m.permute π).fv = m.fv.image π := by
    induction m with
    | var x => simp [permute, fv]
    | app m n ihm ihn => simp [permute, fv, ihm, ihn, Finset.image_union]
    | abs x m ih =>
      simp only [permute, fv, ih]
      rw [Finset.image_sdiff _ _ π.injective]
      simp

omit [DecidableEq Var] in
/-- Permuting successively by `π` and `π'` is permutation by their composition. -/
lemma permute_trans (m : Term Var) (π π' : Equiv.Perm Var) :
  (m.permute π).permute π' = m.permute (π.trans π') := by
    induction m <;> simp_all [permute]

/-- A transposition acts on terms in the same way as `Term.swap`. -/
lemma permute_swap (m : Term Var) (x y : Var) : m.permute (Equiv.swap x y) = m.swap x y := by
  induction m <;> simp_all [permute, swap, Equiv.swap_apply_def]

-- First 4 case examination of example 1
lemma desired_condition_cases_z_ne_u_or_v {E E' : Term Var} {a b u v z : Var}
  (hm1 : z ∉ E.vars ∪ E'.vars ∪ {a, b})
  (h2 : ((E.rename a z).swap u v) =α ((E'.rename b z).swap u v))
  (hzu : z ≠ u)
  (hzv : z ≠ v)
  : ((E.swap u v).swap (Equiv.swap u v a) z) =α ((E'.swap u v).swap (Equiv.swap u v b) z) := by
    have hzb : z ≠ b := by simp_all
    have hza : z ≠ a := by simp_all
    have z_h1 : z ∉ (E.swap u v).vars := by exact not_mem_vars_swap hzu hzv (by simp_all)
    have z_h2 : z ∉ (E'.swap u v).vars := by exact not_mem_vars_swap hzu hzv (by simp_all)
    rw [swap_eq_rename_of_not_mem_vars z_h1]
    rw [swap_eq_rename_of_not_mem_vars z_h2]
    rw [← swap_rename_comm' (by grind) (by grind)] at h2
    rw [← swap_rename_comm' (by grind) (by grind)] at h2
    have ha : a = u ∨ a = v ∨ (a ≠ u ∧ a ≠ v) := by grind
    have hb : b = u ∨ b = v ∨ (b ≠ u ∧ b ≠ v) := by grind
    rcases ha with h' | h' | ⟨hau, hav⟩
    · rcases hb with h'' | h'' | ⟨hbu, hbv⟩ <;> simp_all
    · rcases hb with h'' | h'' | ⟨hbu, hbv⟩ <;> simp_all
    · rcases hb with h'' | h'' | ⟨hbu, hbv⟩ <;> simp_all

-- example 1: use z as witness
lemma alphaEquiv_swap_preserve_abs_fresh {E E' : Term Var} {a b u v z : Var}
  (hm : z ∉ E.vars ∪ E'.vars ∪ {a, b})
  (hbody : ((E.rename a z).swap u v) =α ((E'.rename b z).swap u v))
  (hzu : z ≠ u) (hzv : z ≠ v) :
  ((Term.abs a E).swap u v) =α ((Term.abs b E').swap u v) := by
    have hzE : z ∉ (E.swap u v).vars := not_mem_vars_swap hzu hzv (by simp_all)
    have hzE' : z ∉ (E'.swap u v).vars := not_mem_vars_swap hzu hzv (by simp_all)
    have hren := desired_condition_cases_z_ne_u_or_v hm hbody hzu hzv
    rw [swap_eq_rename_of_not_mem_vars hzE, swap_eq_rename_of_not_mem_vars hzE'] at hren
    simp only [Term.swap]
    apply AlphaEquiv.abs (y := z)
    · simp_all [Finset.mem_union, Finset.mem_insert, swap]
      grind
    · exact hren

-- example 2: use v as witness
lemma alphaEquiv_swap_preserve_abs_fresh_z_eq_u {E E' : Term Var} {a b u v : Var}
  (hm : u ∉ E.vars ∪ E'.vars ∪ {a, b})
  (hbody : ((E.rename a u).swap u v) =α ((E'.rename b u).swap u v))
  (hau : a ≠ u) (hav : a ≠ v) (hbu : b ≠ u) (hbv : b ≠ v) :
  ((Term.abs a E).swap u v) =α ((Term.abs b E').swap u v) := by
    have huE : u ∉ E.vars := by simp_all
    have huE' : u ∉ E'.vars := by simp_all
    rw [← swap_eq_rename_of_not_mem_vars huE, ← swap_eq_rename_of_not_mem_vars huE'] at hbody
    rw [swap_comm (m := E) (x := a) (y := u), swap_comm (m := E') (x := b) (y := u)] at hbody
    rw [← swap_comp_eq_of_ne hau hav, ← swap_comp_eq_of_ne hbu hbv] at hbody
    rw [swap_comm (m := E.swap u v) (x := v) (y := a)] at hbody
    rw [swap_comm (m := E'.swap u v) (x := v) (y := b)] at hbody
    have hvE : v ∉ (E.swap u v).vars := not_mem_swap_target huE
    have hvE' : v ∉ (E'.swap u v).vars := not_mem_swap_target huE'
    rw [swap_eq_rename_of_not_mem_vars hvE, swap_eq_rename_of_not_mem_vars hvE'] at hbody
    apply AlphaEquiv.abs (y := v) <;> (simp_all [swap]; grind)

-- example 3
lemma alphaEquiv_swap_preserve_abs_b_eq_u {E E' : Term Var} {a u v : Var}
  (hm : v ∉ E.vars ∪ E'.vars ∪ {a})
  (hbody : ((E.rename a v).swap u v) =α ((E'.rename u v).swap u v))
  (hau : a ≠ u) (hav : a ≠ v) (huv : u ≠ v) :
  ((Term.abs a E).swap u v) =α ((Term.abs u E').swap u v) := by
    have hvE : v ∉ E.vars := by simp_all
    have hvE' : v ∉ E'.vars := by simp_all
    have huE : u ∉ (E.swap u v).vars := by rw [swap_comm]; exact not_mem_swap_target hvE
    have huE' : u ∉ (E'.swap u v).vars := by rw [swap_comm]; exact not_mem_swap_target hvE'
    have hL : (E.swap u v).rename a u = (E.rename a v).swap u v := by
      have h := @swap_rename_comm _ _ E u v a v
      simp_all
      grind
    have hR : (E'.swap u v).rename v u = (E'.rename u v).swap u v := by
      have h := @swap_rename_comm _ _ E' u v u v
      simp_all
    have hbody' : ((E.swap u v).rename a u) =α ((E'.swap u v).rename v u) := by
      rw [hL, hR]
      exact hbody
    apply AlphaEquiv.abs (y := u)
    · simp_all [Finset.mem_union, Finset.mem_insert, swap]
      grind
    · simp_all [swap]
      grind

-- example 4
lemma alphaEquiv_swap_preserve_abs_a_eq_b_eq_u {E E' : Term Var} {u v : Var}
  (hm : v ∉ E.vars ∪ E'.vars ∪ {u})
  (ih : ((E.rename u v).swap u v) =α ((E'.rename u v).swap u v)) (huv : u ≠ v) :
  ((Term.abs u E).swap u v) =α ((Term.abs u E').swap u v) := by
    have hvE : v ∉ E.vars := by simp_all
    have hvE' : v ∉ E'.vars := by simp_all
    rw [← swap_eq_rename_of_not_mem_vars hvE, ← swap_eq_rename_of_not_mem_vars hvE'] at ih
    rw [swap_involutive, swap_involutive] at ih
    -- now have ih : E =α E'
    have huE : u ∉ (E.swap u v).vars := by
      have h := not_mem_swap_target (u := v) (v := u) hvE
      rwa [swap_comm] at h
    have huE' : u ∉ (E'.swap u v).vars := by
      have h := not_mem_swap_target (u := v) (v := u) hvE'
      rw [swap_comm] at h
      exact h
    apply AlphaEquiv.abs (y := u)
    · simp_all [swap]
    · simp only [Equiv.swap_apply_left]
      change ((E.swap u v).rename v u) =α ((E'.swap u v).rename v u)
      rw [← swap_eq_rename_of_not_mem_vars (m := E.swap u v) (x := v) (y := u) huE]
      rw [← swap_eq_rename_of_not_mem_vars (m := E'.swap u v) (x := v) (y := u) huE']
      nth_rw 2 [swap_comm]
      nth_rw 4 [swap_comm]
      rw [swap_involutive, swap_involutive]
      exact ih

/-- Symmetry of α-equivalence. -/
theorem AlphaEquiv.symm {m n : Term Var} : m =α n → n =α m := by
  intro h
  induction h with
  | @var x => apply AlphaEquiv.var
  | @abs y x1 x2 m1 m2 hy h ih => apply AlphaEquiv.abs (y := y) (by simp_all) ih
  | @app m1 n1 m2 n2 hwm1 hwn1 hwm2 hwn2 => apply AlphaEquiv.app hwm2 hwn2

/-- Lemma 6.1 [Crole2012]: Swap (transposition) preserves α-equivalence. -/
lemma AlphaEquiv.swap_preserve {m m' : Term Var} {u v : Var} :
  m =α m' → (m.swap u v) =α (m'.swap u v) := by
    intro h1
    by_cases h2 : u = v
    · simp_all
    · change u ≠ v at h2
      induction h1 with
      | var => apply AlphaEquiv.var
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

variable [HasFresh Var]

/-- Reflexivity of α-equivalence. -/
theorem AlphaEquiv.refl (m : Term Var) : m =α m := by
  induction m with
  | var x => apply AlphaEquiv.var
  | abs x m ih =>
    obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m.vars ∪ {x})
    apply AlphaEquiv.abs (y := z) (by simp_all)
    rw [← swap_eq_rename_of_not_mem_vars (by simp_all)]
    exact AlphaEquiv.swap_preserve ih
  | app m n m_ih n_ih => apply AlphaEquiv.app m_ih n_ih

/-- Renaming α-equivalent terms produces α-equivalent terms. -/
theorem AlphaEquiv.rename_preserve (m n : Term Var) (x y : Var) :
    y ∉ m.vars ∪ n.vars → m =α n → (m.rename x y) =α (n.rename x y) := by
  refine (WellFounded.induction sizeOfWFRel.wf m
    (C := fun m => ∀ (n : Term Var) (x y : Var), y ∉ m.vars ∪ n.vars →
      m =α n → (m.rename x y) =α (n.rename x y)) ?_) n x y
  intro m ih n x y hy h
  by_cases hyx : y = x
  · grind [rename_same]
  cases h with
  | @var z => apply AlphaEquiv.refl
  | @abs z x1 x2 m1 m2 hz hbody =>
    obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m1.vars ∪ m2.vars ∪ {x1, x2, x, y, z})
    apply AlphaEquiv.abs (y := w)
    · grind [rename_vars]
    rw [rename_comm2, rename_comm2]
    case neg.abs.a =>
      apply ih
      · grind [rename_eq_sizeOf]
      · grind [vars, rename_vars]
      · have hxzw : ((m1.rename x1 z).rename z w) =α ((m2.rename x2 z).rename z w) := by
          apply ih <;> grind [vars, rename_vars, rename_eq_sizeOf]
        grind [rename_concat]
    all_goals grind [vars]
  | @app m1 n1 m2 n2 hm hn =>
    apply AlphaEquiv.app <;> apply ih <;> grind [vars]

lemma AlphaEquiv.abs_congr {m m' : Term Var} {x : Var} :
  m =α m' → (Term.abs x m) =α (Term.abs x m') := by
    intro h
    obtain ⟨y, hy⟩ := HasFresh.fresh_exists (m.vars ∪ m'.vars ∪ {x})
    apply AlphaEquiv.abs (y := y)
    · grind
    · apply AlphaEquiv.rename_preserve <;> grind

omit [DecidableEq Var] [HasFresh Var] in
lemma permute_permute (m : Term Var) (π π' : Equiv.Perm Var) :
  (m.permute π).permute π' = m.permute (π' * π) := by
    induction m with
    | var x => simp [permute]
    | abs x m ih => simp [permute, ih]
    | app m n ih_m ih_n => simp [permute, ih_m, ih_n]

/-- Elimination rule for α-equivalence of abstractions.
    It states that if two abstractions are α-equivalent,
    then their bodies can be renamed to ``any'' fresh variable y and remain α-equivalent.
    This is sometimes easier to use than using by_cases on the equivalence,
    which can only produce the claim for ``some'' fresh y. -/
theorem AlphaEquiv.abs_elim {m1 m2 : Term Var} {x1 x2 y : Var} :
    y ∉ m1.vars ∪ m2.vars ∪ {x1, x2} → (Term.abs x1 m1) =α (Term.abs x2 m2) →
    (m1.rename x1 y) =α (m2.rename x2 y) := by
  intro hy h
  cases h with
  | @abs z _ _ _ _ hz h1 =>
    by_cases hzy : z = y
    · grind
    · have hxzy : ((m1.rename x1 z).rename z y) =α ((m2.rename x2 z).rename z y) := by
        apply AlphaEquiv.rename_preserve <;> grind [AlphaEquiv.rename_preserve, rename_vars]
      grind [rename_concat, rename_vars]

-- TODO render closer on original
/-- Transitivity of α-equivalence. -/
theorem AlphaEquiv.trans {m n p : Term Var} :
    m =α n → n =α p → m =α p := by
  refine (WellFounded.induction sizeOfWFRel.wf m
    (C := fun m => ∀ (n p : Term Var), m =α n → n =α p → m =α p) ?_) n p
  intro m ih n p hmn hnp
  cases m with
  | var x =>
    cases hmn with
    | @var x => assumption
  | abs x1 m1 =>
    obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m1.vars ∪ {x1} ∪ n.vars ∪ p.vars)
    have hmn' := hmn
    cases hmn' with
    | @abs y x1 x2 m1 m2 hy h1 =>
      have hnp' := hnp
      cases hnp' with
      | @abs z x2 x3 m2 m3 hz h2 =>
        apply AlphaEquiv.abs (y := w)
        · grind [vars, rename_unused, rename_vars, rename_concat]
        apply ih _ ?_ (m2.rename x2 w) <;>
        grind [AlphaEquiv.abs_elim, vars, rename_vars, rename_eq_sizeOf]
  | app m1 m2 =>
    cases hmn with
    | @app m1 n1 m2 n2 hmn1 hmn2 =>
      cases hnp with
      | @app n1 p1 n2 p2 hnp1 hnp2 =>
        apply AlphaEquiv.app
        · apply ih _ ?_ n1 <;> grind [vars, rename_vars]
        · apply ih _ ?_ n2 <;> grind [vars, rename_vars]

/-- Renaming a non-free variable results in an α-equivalent term -/
theorem AlphaEquiv.rename_non_fv {m : Term Var} {x y : Var} :
    x ∉ m.fv → y ∉ m.vars → m =α (m.rename x y) := by
  intro hx hy
  induction m with
  | var z =>
    have hzx : z ≠ x := by
      grind [fv]
    simpa [rename, hzx] using AlphaEquiv.var
  | abs z m ih =>
    by_cases hzx : z = x
    · subst z
      simp only [rename, ↓reduceIte]
      obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m.vars ∪ {x, y})
      apply AlphaEquiv.abs (y := w)
      · grind [rename_unused, rename_vars]
      rw [rename_concat] <;> grind [vars, AlphaEquiv.refl]
    · simp only [rename, hzx, ↓reduceIte]
      obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m.vars ∪ {x, y, z})
      apply AlphaEquiv.abs (y := w)
      · grind [rename_unused, rename_vars]
      apply AlphaEquiv.rename_preserve <;> grind [vars, rename_vars, fv]
  | app m1 m2 ih1 ih2 =>
    apply AlphaEquiv.app
    · apply ih1 <;> grind [vars, fv]
    · apply ih2 <;> grind [vars, fv]

/-- Abstracting over an arbitrary non-free variable results in the same term,
    modulo α-equivalence. -/
theorem AlphaEquiv.abs_non_fv {m1 m2 : Term Var} {x1 x2 : Var} :
    m1 =α m2 → x1 ∉ m1.fv → x2 ∉ m2.fv → (Term.abs x1 m1) =α (Term.abs x2 m2) := by
  intro hm hx1 hx2
  obtain ⟨y, hy⟩ := HasFresh.fresh_exists (m1.vars ∪ m2.vars ∪ {x1, x2})
  apply AlphaEquiv.abs (y := y)
  · grind
  apply AlphaEquiv.trans (n := m1)
  · grind [rename_non_fv, AlphaEquiv.symm]
  apply AlphaEquiv.trans (n := m2) <;> grind [rename_non_fv]

/-- Renaming an abstraction leads to an α-equivalent term. -/
theorem AlphaEquiv.abs_rename {m : Term Var} {x y : Var} :
    y ∉ m.vars ∪ {x} → (Term.abs x m) =α (Term.abs y (m.rename x y)) := by
  intro hy
  obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m.vars ∪ {x, y})
  apply AlphaEquiv.abs (y := z) <;> grind [vars, rename_vars, rename_concat, AlphaEquiv.refl]

omit [DecidableEq Var] [HasFresh Var] in
/-- Any `Term` can be obtained by filling a `Context` with a variable. This proves that `Context`
completely captures the syntax of terms. -/
theorem Context.complete (m : Term Var) :
    ∃ (c : Context Var) (x : Var), m = (c.fill (var x)) := by
  induction m with
  | var x => exists hole, x
  | abs x n ih =>
    obtain ⟨c', y, ih⟩ := ih
    exists Context.abs x c', y
    rw [ih, fill]
  | app n₁ n₂ ih₁ ih₂ =>
    obtain ⟨c₁, x₁, ih₁⟩ := ih₁
    exists Context.appL c₁ n₂, x₁
    rw [ih₁, fill]

omit [HasFresh Var] in
/-- The set of variables after filling a context. -/
theorem Context.fill_vars {c : Context Var} {m : Term Var} :
    (c.fill m).vars = c.vars ∪ m.vars := by
  induction c <;> grind [Context.fill, Context.vars, Term.vars]

/-- α-equivalence is preserved under context filling. -/
theorem AlphaEquiv.context {m n : Term Var} {c : Context Var} :
    m =α n → (c.fill m) =α (c.fill n) := by
  intro h
  induction c with
  | hole => assumption
  | abs x c ih =>
    simp only [Context.fill]
    obtain ⟨y, hy⟩ := HasFresh.fresh_exists (m.vars ∪ n.vars ∪ c.vars ∪ {x})
    apply AlphaEquiv.abs (y := y) <;> grind [Context.fill_vars, rename_preserve]
  | appL c m ih =>
    apply AlphaEquiv.app <;> grind [AlphaEquiv.app, AlphaEquiv.refl, vars]
  | appR m c ih =>
    apply AlphaEquiv.app <;> grind [AlphaEquiv.app, AlphaEquiv.refl, vars]

/-- The functional definition of substitution satisfies the relational definition of substitution.
-/
theorem Subst.function_to_relation {m r : Term Var} {x : Var} :
    m.Subst x r (m[x := r]) := by
  refine WellFounded.induction (C := fun m => m.Subst x r (m[x := r])) sizeOfWFRel.wf m ?_
  simp only; intro m ih
  cases m with
  | var y =>
    by_cases hyx : y = x
    · subst y
      simp only [← subst_def, subst.eq_1, ↓reduceIte]
      apply Subst.varHit
    · simp [hyx, ← subst_def]
      grind [Subst.varMiss]
  | abs y m =>
    by_cases hyx : y = x
    · subst y
      simp only [← subst_def, subst.eq_2, ↓reduceIte]
      apply Subst.absShadow
    · simp only [← subst_def, subst.eq_2, hyx, ↓reduceIte, Finset.union_insert]
      by_cases hyr : y ∈ r.fv
      · simp only [hyr]
        have hz := fresh_notMem (insert x (insert y (m.vars ∪ r.vars)))
        set z := fresh (insert x (insert y (m.vars ∪ r.vars)))
        apply Subst.alpha (m := abs z (m.rename y z)) (r := r) (n := abs z ((m.rename y z)[x := r]))
        · have h1 : abs z (m.rename y z) = (abs y m).rename y z := by
            simp [rename]
          grind [AlphaEquiv.symm, AlphaEquiv.rename_non_fv, vars, fv]
        · grind [AlphaEquiv.refl]
        · grind [AlphaEquiv.refl]
        · apply Subst.absIn
          · grind [vars, fv, vars_either_fv_or_bv]
          apply ih
          grind [rename_eq_sizeOf]
      · simp only [hyr]
        apply Subst.absIn
        · grind [vars, fv, vars_either_fv_or_bv]
        apply ih
        grind
  | app m1 m2 =>
    simp only [← subst_def, subst.eq_3]
    apply Subst.app <;> apply ih <;> grind

/-- Substituting a non-free variable has no effect. -/
theorem subst.non_free {m r : Term Var} {x : Var} :
    x ∉ m.fv → (m[x := r]) =α m := by
  refine WellFounded.induction (C := fun m => x ∉ m.fv → (m[x := r]) =α m) sizeOfWFRel.wf m ?_
  simp only; intro m ih hx
  cases m with
  | var y =>
    have hyx : y ≠ x := by
      grind [fv]
    simp only [← subst_def, subst.eq_1, hyx, ↓reduceIte]
    apply AlphaEquiv.var
  | abs y m =>
    by_cases hyx : y = x
    · subst y
      simp only [← subst_def, subst.eq_2, ↓reduceIte]
      apply AlphaEquiv.refl
    · by_cases hyr : y ∈ r.fv
      · simp only [← subst_def, subst.eq_2, hyx, ↓reduceIte, hyr, not_true_eq_false,
          Finset.union_insert, Finset.union_singleton]
        have hz := fresh_notMem (insert x (insert y (m.vars ∪ r.vars)))
        set z := fresh (insert x (insert y (m.vars ∪ r.vars)))
        obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m.vars ∪ r.vars ∪ ((m.rename y z).subst x r).vars
          ∪ {x, y, z})
        apply AlphaEquiv.abs (y := w)
        · grind [vars, rename_unused, rename_vars]
        apply AlphaEquiv.trans (n := ((m.rename y z).rename z w))
        · apply AlphaEquiv.rename_preserve
          · grind [vars, rename_vars, fv]
          apply ih <;> grind [fv, rename_fv, rename_eq_sizeOf]
        · grind [rename_concat, AlphaEquiv.refl]
      · simp only [← subst_def, subst.eq_2, hyx, ↓reduceIte, hyr, not_false_eq_true]
        apply AlphaEquiv.context (c := Context.abs y Context.hole)
        apply ih <;> grind [fv]
  | app m1 m2 =>
    simp only [← subst_def, subst.eq_3]
    apply AlphaEquiv.app <;> apply ih <;> grind [fv]

lemma subst.abs_fresh_helper {m r : Term Var} {x y z : Var} :
    z ∉ m.vars ∪ r.vars ∪ {x, y} →
    ((Term.abs y m)[x := r]) =α (Term.abs z ((m.rename y z)[x := r]))
    ∧ (y ∉ r.fv ∪ {x} → (Term.abs y (m[x := r])) =α (Term.abs z ((m.rename y z)[x := r]))) := by
  refine (WellFounded.induction sizeOfWFRel.wf m
    (C := fun m => ∀ (r : Term Var) (x y z : Var),
    z ∉ m.vars ∪ r.vars ∪ {x, y} →
    ((Term.abs y m)[x := r]) =α (Term.abs z ((m.rename y z)[x := r]))
    ∧ (y ∉ r.fv ∪ {x} → (Term.abs y (m[x := r])) =α (Term.abs z ((m.rename y z)[x := r])))) ?_)
    r x y z
  intro m ih r x y z hz
  have hright : ∀ (m' : Term Var) (y' : Var), sizeOf m' = sizeOf m → z ∉ m'.vars ∪ r.vars ∪ {x, y'}
    → y' ∉ r.fv ∪ {x} → (Term.abs y' (m'[x:=r])) =α (Term.abs z ((m'.rename y' z)[x:=r])) := by
    intro m' y' hm' hz hy'
    cases m' with
    | var w =>
      by_cases hwx : w = x
      · subst w
        have hxy' : x ≠ y' := by grind
        rw [rename]
        simp only [← subst_def, subst.eq_1, ↓reduceIte, hxy']
        apply AlphaEquiv.abs_non_fv <;> grind [vars_either_fv_or_bv, AlphaEquiv.refl]
      · simp only [← subst_def, subst.eq_1, hwx, ↓reduceIte]
        rw [rename]
        by_cases hwy' : w = y'
        · subst w
          have hzx : z ≠ x := by grind
          simp only [↓reduceIte, subst.eq_1, hzx]
          obtain ⟨v, hv⟩ := HasFresh.fresh_exists ({y', z})
          apply AlphaEquiv.abs (y := v) <;> grind [vars, rename, AlphaEquiv.var]
        · simp only [hwy', ↓reduceIte, subst.eq_1, hwx]
          apply AlphaEquiv.abs_non_fv <;> grind [vars_either_fv_or_bv, AlphaEquiv.refl, Term.fv]
    | app m1 m2 =>
      obtain ⟨w, hw⟩ := HasFresh.fresh_exists
        ((m1.app m2)[x := r].vars ∪ (((m1.app m2).rename y' z)[x := r]).vars
        ∪ m1[x := r].vars ∪ m2[x := r].vars ∪ (m1.rename y' z)[x := r].vars
        ∪ (m2.rename y' z)[x := r].vars ∪ {y', z})
      apply AlphaEquiv.abs (y := w)
      · grind
      simp only [← subst_def, subst.eq_3, rename]
      apply AlphaEquiv.app <;> apply AlphaEquiv.abs_elim <;> grind [vars, rename_vars]
    | abs w m1 =>
      by_cases hwy' : w = y'
      · subst w
        rw [rename]
        have hy'x : y' ≠ x := by grind
        have hy'r : y' ∉ r.fv := by grind
        have hzx : z ≠ x := by grind
        have hzr : z ∉ r.fv := by grind [vars_either_fv_or_bv]
        simp only [← subst_def, subst.eq_2, hy'x, ↓reduceIte, hy'r, not_false_eq_true, hzx, hzr]
        apply AlphaEquiv.abs_non_fv
        · apply (ih _ _ _ _ _ _ _).right <;> grind [vars]
        · grind [fv]
        · grind [fv]
      · rw [rename]
        simp only [hwy', ↓reduceIte]
        by_cases hwx : w = x
        · subst w
          simp only [← subst_def, subst, ↓reduceIte]
          apply AlphaEquiv.trans (n := Term.abs z ((Term.abs x m1).rename y' z))
          · grind [AlphaEquiv.abs_rename]
          · grind [rename, AlphaEquiv.refl]
        · by_cases hwr : w ∈ r.fv
          · obtain ⟨v, hv⟩ := HasFresh.fresh_exists (m1.vars ∪ r.vars ∪ {x, y', z, w})
            have hl : (Term.abs y' (((Term.abs w m1)[x := r]))) =α
                (Term.abs y' (Term.abs v ((m1.rename w v)[x := r]))) := by
              apply AlphaEquiv.context (c := Context.abs y' Context.hole)
              apply (ih _ _ _ _ _ _ _).left <;> grind
            have hr : (Term.abs z (Term.abs v (((m1.rename y' z).rename w v)[x := r])))
              =α (Term.abs z ((Term.abs w (m1.rename y' z))[x := r])) := by
              apply AlphaEquiv.context (c := Context.abs z Context.hole)
              apply AlphaEquiv.symm
              apply (ih _ _ _ _ _ _ _).left <;> grind [rename_vars, rename_eq_sizeOf]
            have hmid : (Term.abs y' (Term.abs v ((m1.rename w v)[x := r]))) =α
                (Term.abs z (Term.abs v (((m1.rename y' z).rename w v)[x := r]))) := by
              obtain ⟨u, hu⟩ := HasFresh.fresh_exists
                ((Term.abs v ((m1.rename w v)[x := r])).vars ∪
                (Term.abs v (((m1.rename y' z).rename w v)[x := r])).vars ∪
                ((m1.rename w v).rename y' z)[x:=r].vars ∪ {y', z})
              apply AlphaEquiv.abs (y := u)
              · grind
              · have hvy' : v ≠ y' := by grind
                have hvz : v ≠ z := by grind
                simp only [rename, hvy', hvz, ↓reduceIte]
                apply AlphaEquiv.context (c := Context.abs v Context.hole)
                apply AlphaEquiv.trans (n := (((m1.rename w v).rename y' z)[x := r]).rename z u)
                · apply AlphaEquiv.abs_elim
                  · grind  [vars]
                  · apply (ih _ _ _ _ _ _ _).right <;> grind [vars, rename_vars, rename_eq_sizeOf]
                · apply AlphaEquiv.rename_preserve
                  · grind [vars]
                  · rw [rename_comm] <;> grind [vars, AlphaEquiv.refl]
            exact AlphaEquiv.trans hl <| AlphaEquiv.trans hmid hr
          · obtain ⟨v, hv⟩ := HasFresh.fresh_exists
              (m1[x:=r].vars ∪ (m1.rename y' z)[x:=r].vars ∪ ((Term.abs w m1)[x := r]).vars ∪
              ((Term.abs w (m1.rename y' z))[x := r]).vars ∪ {y', z})
            apply AlphaEquiv.abs (y := v)
            · grind [vars, rename_vars]
            · have hwz : w ≠ z := by grind [vars]
              simp only [← subst_def, subst, hwx, ↓reduceIte, hwr, not_false_eq_true, rename, hwy',
                hwz]
              apply AlphaEquiv.context (c := Context.abs w Context.hole)
              apply AlphaEquiv.abs_elim <;> grind [vars]
  have hleft : ((Term.abs y m)[x:=r]) =α (Term.abs z ((m.rename y z)[x:=r])) := by
    by_cases hyx : y = x
    · subst y
      simp only [← subst_def, subst.eq_2, ↓reduceIte]
      obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m.vars ∪ r.vars ∪ ((m.rename x z).subst x r).vars ∪
        {x, z})
      apply AlphaEquiv.abs (y := w)
      · grind [vars, rename_unused, rename_vars]
      · apply AlphaEquiv.trans (n := ((m.rename x z).rename z w))
        · grind [AlphaEquiv.refl, rename_concat]
        · apply AlphaEquiv.rename_preserve
          · grind [rename_vars]
          · apply AlphaEquiv.symm
            apply subst.non_free
            grind [fv, rename_fv, rename_eq_sizeOf]
    · by_cases hyr : y ∈ r.fv
      · simp only [← subst_def, subst.eq_2, hyx, ↓reduceIte, hyr, not_true_eq_false,
          Finset.union_insert, Finset.union_singleton]
        have hw := fresh_notMem (insert x (insert y (m.vars ∪ r.vars)))
        set w := fresh (insert x (insert y (m.vars ∪ r.vars)))
        by_cases hzw' : z = w
        · subst z
          apply AlphaEquiv.refl
        · apply AlphaEquiv.trans (n := (Term.abs z (((m.rename y w).rename w z)[x := r])))
          · apply hright <;>
              grind [rename_eq_sizeOf, vars_either_fv_or_bv, rename_vars]
          · rw [rename_concat] <;> grind [AlphaEquiv.refl]
      · simp only [← subst_def, subst.eq_2, hyx, ↓reduceIte, hyr, not_false_eq_true]
        apply hright <;> grind
  exact ⟨hleft, hright m y (by rfl) (by grind)⟩

/-- Modulo α-equivalence, substituting an abstraction falls back to the fresh variable case only.
    With this lemma, the three cases in the definition of subst can be reduced to one.
-/
theorem subst.abs_fresh {m r : Term Var} {x y z : Var} :
    z ∉ m.vars ∪ r.vars ∪ {x, y} →
    ((Term.abs y m)[x := r]) =α (Term.abs z ((m.rename y z)[x := r])) := by
  grind [subst.abs_fresh_helper]

/-- Substituting α-equivalent terms produces α-equivalent terms. -/
theorem subst.preserve_AlphaEquiv {m m' r r' : Term Var} {x : Var} :
    m =α m' → r =α r' → (m[x := r]) =α (m'[x := r']) := by
  refine (WellFounded.induction sizeOfWFRel.wf m
    (C := fun m => ∀ (m' r r' : Term Var) (x : Var),
      m =α m' → r =α r' → (m[x := r]) =α (m'[x := r'])) ?_) m' r r' x
  intro m ih m' r r' x hmm' hrr'
  have hmm'' := hmm'
  cases hmm'' with
  | @var y =>
    by_cases hyx : y = x
    · simp only [← subst_def, subst, ↓reduceIte, hyx]
      assumption
    · simp only [← subst_def, subst, hyx]
      apply AlphaEquiv.refl
  | @abs z y y' m m' hz h1 =>
    obtain ⟨w, hw⟩ := HasFresh.fresh_exists (m.vars ∪ m'.vars ∪ r.vars ∪ r'.vars ∪ {x, y, y'})
    have h2 : ((Term.abs y m)[x := r]) =α (Term.abs w ((m.rename y w)[x := r])) := by
      grind [subst.abs_fresh]
    have h2' : ((Term.abs y' m')[x := r']) =α
        (Term.abs w ((m'.rename y' w)[x := r'])) := by
      grind [subst.abs_fresh]
    have hbody : (m.rename y w) =α (m'.rename y' w) := by
      apply AlphaEquiv.abs_elim <;> grind
    have h3 :
        (Term.abs w ((m.rename y w)[x := r])) =α (Term.abs w ((m'.rename y' w)[x := r'])) := by
      apply AlphaEquiv.context (c := Context.abs w Context.hole)
      apply ih <;> grind [rename_eq_sizeOf]
    apply AlphaEquiv.trans (n := (Term.abs w ((m.rename y w)[x := r]))) <;> try assumption
    apply AlphaEquiv.trans (n := (Term.abs w ((m'.rename y' w)[x := r']))) <;> try assumption
    apply AlphaEquiv.symm
    assumption
  | @app m m' n n' hm hn =>
    simp only [← subst_def, subst]
    apply AlphaEquiv.app <;> apply ih <;> grind

/-- The relational definition of substitution coincides with the functional definition of
    substitution, modulo α-equivalence. -/
theorem Subst.relation_iff_function {m n r : Term Var} {x : Var} :
    m.Subst x r n ↔ n =α (m[x := r]) := by
  constructor
  · intro h
    induction h with
    | @varHit x r =>
      simp only [← subst_def, subst, ↓reduceIte]
      apply AlphaEquiv.refl
    | @varMiss x y r hyx =>
      simp only [← subst_def, subst, hyx, ↓reduceIte]
      apply AlphaEquiv.refl
    | @absShadow x m r =>
      simp only [← subst_def, subst, ↓reduceIte]
      apply AlphaEquiv.refl
    | @absIn x y m r m' hy h ih =>
      have hyx : y ≠ x := by grind
      have hyr : y ∉ r.fv := by grind
      simp only [← subst_def, subst, hyx, ↓reduceIte, hyr, not_false_eq_true]
      apply AlphaEquiv.context (c := Context.abs y Context.hole)
      assumption
    | @app m n x r m' n' h1 h2 ih1 ih2 =>
      simp only [← subst_def, subst]
      apply AlphaEquiv.app <;> assumption
    | @alpha m m' r r' n n' x hm hr hn h ih =>
      apply AlphaEquiv.trans (n := n)
      · grind [AlphaEquiv.symm]
      apply AlphaEquiv.trans (n := m[x := r]) <;> grind [subst.preserve_AlphaEquiv]
  · intro h
    apply Subst.alpha (m := m) (r := r) (n := m[x := r]) <;> grind [AlphaEquiv.symm,
      AlphaEquiv.refl, Subst.function_to_relation]

/-- Commutativity of substitution (a.k.a. the substitution lemma) -/
theorem subst.commutativity {m r1 r2 : Term Var} {x y : Var} :
    x ∉ r2.fv ∪ {y} → ((m[x := r1])[y := r2]) =α ((m[y := r2])[x := (r1[y := r2])]) := by
  refine WellFounded.induction sizeOfWFRel.wf m
    (C := fun m => ∀ (r1 r2 : Term Var) (x y : Var),
      x ∉ r2.fv ∪ {y} →
      ((m[x := r1])[y := r2]) =α ((m[y := r2])[x := (r1[y := r2])])) ?_ r1 r2 x y
  intro m ih r1 r2 x y hxy
  cases m with
  | var z =>
    by_cases hzx : z = x
    · subst z
      have hxy' : x ≠ y := by grind
      simp only [← subst_def, subst.eq_1, ↓reduceIte, hxy']
      apply AlphaEquiv.refl
    · by_cases hzy : z = y
      · subst z
        simp only [← subst_def, subst.eq_1, hzx, ↓reduceIte]
        apply AlphaEquiv.symm
        apply subst.non_free
        grind
      · simp only [← subst_def, subst.eq_1, hzx, hzy, ↓reduceIte]
        apply AlphaEquiv.refl
  | abs z m =>
    obtain ⟨w, hw⟩ := HasFresh.fresh_exists
      (m.vars ∪ r1.vars ∪ r2.vars ∪ (r1[y := r2]).vars ∪ {x, y, z})
    have hl : (((Term.abs z m)[x := r1])[y := r2]) =α
      (Term.abs w (((m.rename z w)[x := r1])[y := r2])) := by
      apply AlphaEquiv.trans (n := (((Term.abs w ((m.rename z w)[x := r1]))[y := r2])))
      · apply subst.preserve_AlphaEquiv
        · apply subst.abs_fresh
          grind
        · apply AlphaEquiv.refl
      · have hwy : w ≠ y := by grind
        have hwr2 : w ∉ r2.fv := by grind [vars_either_fv_or_bv]
        simp only [← subst_def, subst.eq_2, hwy, ↓reduceIte, hwr2, not_false_eq_true]
        apply AlphaEquiv.refl
    have hr : (Term.abs w (((m.rename z w)[y := r2])[x := (r1[y := r2])]))
      =α (((Term.abs z m)[y := r2])[x := (r1[y := r2])]) := by
      apply AlphaEquiv.symm
      apply AlphaEquiv.trans (n := ((Term.abs w ((m.rename z w)[y := r2]))[x := (r1[y := r2])]))
      · apply subst.preserve_AlphaEquiv
        · apply subst.abs_fresh
          grind
        · apply AlphaEquiv.refl
      · have hwx : w ≠ x := by grind
        have hwr : w ∉ (r1.subst y r2).fv := by grind [vars_either_fv_or_bv]
        simp only [← subst_def, subst.eq_2, hwx, ↓reduceIte, hwr, not_false_eq_true]
        apply AlphaEquiv.refl
    have hmid : (Term.abs w (((m.rename z w)[x := r1])[y := r2])) =α
      (Term.abs w (((m.rename z w)[y := r2])[x := (r1[y := r2])])) := by
      apply AlphaEquiv.context (c := Context.abs w Context.hole)
      apply ih <;> grind [rename_eq_sizeOf]
    exact AlphaEquiv.trans hl <| AlphaEquiv.trans hmid hr
  | app m1 m2 =>
    simp only [← subst_def, subst.eq_3]
    apply AlphaEquiv.app <;> apply ih <;> grind

end LambdaCalculus.Named.Untyped.Term

end Cslib
