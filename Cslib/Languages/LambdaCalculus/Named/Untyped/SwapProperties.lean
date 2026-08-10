/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivDefs
public import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties

/-! # Properties of the swap (transposition) operation on lambda terms

Helper lemmas for reasoning about `Term.swap` and its interaction with
`AlphaEquiv`, `rename`, `vars`, and `fv`.

The notion of *atom swapping* (transposition) as the basis for defining α-equivalence
originates from [Gabbay and Pitts, *A New Approach to Abstract Syntax with Variable
Binding*][Gabbay2002] (Section 2, page 3). The key observation is that α-equivalence can
be defined using the notion of atom swapping in lieu of the traditional
renaming/substitution approach.

The swap (transposition) operation `m.swap x y` implements the permutation action
`(x y) · E` from [Crole2012] (Section 2). It simultaneously replaces all occurrences
of `x` with `y` and vice versa throughout a term.

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012], Sections 2 and 6
* [M. Gabbay and A. Pitts, *A New Approach to Abstract Syntax with Variable
  Binding*][Gabbay2002], Section 2
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.Named.Untyped.Term

def agreementSet (f g : Var → Var) : Set Var := { x | f x = g x }
def disagreementSet (f g : Var → Var) : Set Var := { x | f x ≠ g x }

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

lemma AlphaEquiv.abs_congr [HasFresh Var] {m m' : Term Var} {x : Var} :
  m =α m' → (Term.abs x m) =α (Term.abs x m') := by
    intro h
    obtain ⟨y, hy⟩ := HasFresh.fresh_exists (m.vars ∪ m'.vars ∪ {x})
    apply AlphaEquiv.abs (y := y)
    · grind
    · apply AlphaEquiv.rename_preserve <;> grind

omit [DecidableEq Var] in
lemma permute_permute (m : Term Var) (π π' : Equiv.Perm Var) :
  (m.permute π).permute π' = m.permute (π' * π) := by
    induction m with
    | var x => simp [permute]
    | abs x m ih => simp [permute, ih]
    | app m n ih_m ih_n => simp [permute, ih_m, ih_n]

end LambdaCalculus.Named.Untyped.Term

end Cslib
