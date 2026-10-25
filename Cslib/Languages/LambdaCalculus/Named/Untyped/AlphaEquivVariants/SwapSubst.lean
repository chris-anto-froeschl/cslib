/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivVariants.Swap

/-! # Swapping and substitution

The lemmas of Section 6.1 of [Crole2012] that connect the swapping relations with the renaming
relations: swapping with an atom that does not occur is, up to α-equivalence, substitution of
that atom.

## Main results

* `alphaEquivR_swap_subst_var`, `alphaEquivRFresh_swap_subst_var`: Lemmas 6.3 and 6.4.
* `alphaEquiv_swapChain`: Lemma 6.5, with freshness in place of non-occurrence.
* `alphaEquiv_swap_subst_var`: its case `n = 1`, which is what Theorems 4.4 and 4.5 use.
* `alphaEquivR_avoid_var`, `alphaEquiv_avoid_var`: Lemma 6.6, for `∼r` and for `∼p`.

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012], Section 6.1
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped.Term

/-- The `rename` form of Lemma 6.3 [Crole2012]: renaming to an atom that does not occur agrees
with substitution up to `∼r`. -/
lemma alphaEquivR_rename_subst_var {m : Term Var} {x z : Var} (hz : z ∉ m.vars) :
    AlphaEquivR (m.rename x z) (m.subst x (var z)) := by
  induction m with
  | var y => by_cases hyx : y = x <;> simp [rename, subst, hyx, AlphaEquivR.refl]
  | app m1 m2 ih1 ih2 =>
    simp only [rename, subst]
    exact AlphaEquivR.app (ih1 (by grind [vars])) (ih2 (by grind [vars]))
  | abs y m ih =>
    obtain rfl | hyx := eq_or_ne y x
    · -- The binder is renamed, and the rule `α` relates the two sides.
      simp only [rename, subst, reduceIte]
      exact ((AlphaEquivR.alpha (x' := z) (by grind [vars])).trans
        (AlphaEquivR.abs_congr (ih (by grind [vars])).symm)).symm
    · -- The binder is not `x`, and `z` cannot be captured.
      have hyz : y ≠ z := by grind [vars]
      simp only [rename, subst, hyx, reduceIte, fv, hyz, Finset.mem_singleton, not_false_eq_true]
      exact AlphaEquivR.abs_congr (ih (by grind [vars]))

/-- **Lemma 6.3** [Crole2012]: if `z` does not occur in `m`, then `(z a) · m ∼r m[a := z]`. -/
lemma alphaEquivR_swap_subst_var {m : Term Var} {a z : Var} (hz : z ∉ m.vars) :
    AlphaEquivR (m.swap z a) (m.subst a (var z)) := by
  rw [swap_comm, swap_eq_rename_of_notMem_vars hz]
  exact alphaEquivR_rename_subst_var hz

/-- The `rename` form of Lemma 6.4 [Crole2012]: the induction of `alphaEquivR_rename_subst_var`,
with the rule `α#` in place of `α`. -/
lemma alphaEquivRFresh_rename_subst_var {m : Term Var} {x z : Var} (hz : z ∉ m.vars) :
    AlphaEquivRFresh (m.rename x z) (m.subst x (var z)) := by
  induction m with
  | var y => by_cases hyx : y = x <;> simp [rename, subst, hyx, AlphaEquivRFresh.refl]
  | app m1 m2 ih1 ih2 =>
    simp only [rename, subst]
    exact AlphaEquivRFresh.app (ih1 (by grind [vars])) (ih2 (by grind [vars]))
  | abs y m ih =>
    obtain rfl | hyx := eq_or_ne y x
    · -- `α#` applies because non-occurrence implies freshness.
      simp only [rename, subst, reduceIte]
      exact ((AlphaEquivRFresh.alpha (x' := z) (by grind [vars, vars_eq_fv_union_bv])).trans
        (AlphaEquivRFresh.abs_congr (ih (by grind [vars])).symm)).symm
    · have hyz : y ≠ z := by grind [vars]
      simp only [rename, subst, hyx, reduceIte, fv, hyz, Finset.mem_singleton, not_false_eq_true]
      exact AlphaEquivRFresh.abs_congr (ih (by grind [vars]))

/-- **Lemma 6.4** [Crole2012]: if `z` does not occur in `m`, then `(z a) · m ∼r# m[a := z]`. -/
lemma alphaEquivRFresh_swap_subst_var {m : Term Var} {a z : Var} (hz : z ∉ m.vars) :
    AlphaEquivRFresh (m.swap z a) (m.subst a (var z)) := by
  rw [swap_comm, swap_eq_rename_of_notMem_vars hz]
  exact alphaEquivRFresh_rename_subst_var hz

/-- **Lemma 6.6** [Crole2012]: bound atoms can be renamed so that a given atom that is not free
does not occur at all, up to `∼r`. -/
lemma alphaEquivR_avoid_var {m : Term Var} {a : Var} (ha : a ∉ m.fv) :
    ∃ m', a ∉ m'.vars ∧ AlphaEquivR m' m := by
  induction m with
  | var y => exact ⟨var y, by simp_all [vars, fv], AlphaEquivR.refl⟩
  | app m1 m2 ih1 ih2 =>
    obtain ⟨n1, hn1, he1⟩ := ih1 (by simp_all [fv])
    obtain ⟨n2, hn2, he2⟩ := ih2 (by simp_all [fv])
    exact ⟨app n1 n2, by simp_all [vars], AlphaEquivR.app he1 he2⟩
  | abs y m ih =>
    obtain rfl | hay := eq_or_ne a y
    · -- Crole's case `a = b`. Renaming the binder `a` to an unused `z` renames every occurrence
      -- of `a` at once, so no induction on the size of the term is needed.
      obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m.vars ∪ {a})
      refine ⟨abs z (m.rename a z), ?_, ?_⟩
      · have := notMem_vars_rename (m := m) (x := a) (y := z) (by grind)
        grind [vars]
      · exact (AlphaEquivR.abs_congr (alphaEquivR_rename_subst_var (by grind))).trans
          (AlphaEquivR.alpha (by grind)).symm
    · -- Crole's case `a ∉ free(m)`: the induction hypothesis applies.
      obtain ⟨m', hm', he⟩ := ih (by simp_all [fv])
      exact ⟨abs y m', by grind [vars], AlphaEquivR.abs_congr he⟩

/-- Lemma 6.6 [Crole2012] for `∼p`. It cannot be obtained from `alphaEquivR_avoid_var` through
Theorem 4.4, because the proof of that theorem uses it (through Lemma 6.5). -/
lemma alphaEquiv_avoid_var {m : Term Var} {a : Var} (ha : a ∉ m.fv) :
    ∃ m', a ∉ m'.vars ∧ m' =α m := by
  induction m with
  | var y => exact ⟨var y, by simp_all [vars, fv], AlphaEquiv.refl _⟩
  | app m1 m2 ih1 ih2 =>
    obtain ⟨n1, hn1, he1⟩ := ih1 (by simp_all [fv])
    obtain ⟨n2, hn2, he2⟩ := ih2 (by simp_all [fv])
    exact ⟨app n1 n2, by simp_all [vars], AlphaEquiv.app he1 he2⟩
  | abs y m ih =>
    obtain rfl | hay := eq_or_ne a y
    · obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m.vars ∪ {a})
      refine ⟨abs z (m.rename a z), ?_, (AlphaEquiv.abs_rename hz).symm⟩
      have := notMem_vars_rename (m := m) (x := a) (y := z) (by grind)
      grind [vars]
    · obtain ⟨m', hm', he⟩ := ih (by simp_all [fv])
      exact ⟨abs y m', by grind [vars], AlphaEquiv.abs_congr he⟩

/-- The `∼p` form of Lemma 6.3 [Crole2012], for `rename`: the induction of
`alphaEquivR_rename_subst_var`, with `AlphaEquiv.abs_rename` in place of the rule `α`. -/
lemma rename_alphaEquiv_subst_var {m : Term Var} {x x' : Var} (hx' : x' ∉ m.vars) :
    (m.rename x x') =α (m.subst x (var x')) := by
  induction m with
  | var y =>
    by_cases hyx : y = x <;> simpa only [rename, subst, hyx, reduceIte] using AlphaEquiv.refl _
  | app m1 m2 ih1 ih2 =>
    simp only [rename, subst]
    exact AlphaEquiv.app (ih1 (by grind [vars])) (ih2 (by grind [vars]))
  | abs y m ih =>
    obtain rfl | hyx := eq_or_ne y x
    · -- On the right the substitution is shadowed, on the left the binder is renamed.
      simp only [rename, subst, reduceIte]
      exact (AlphaEquiv.abs_rename (by simp_all [vars])).symm
    · have hyx' : y ≠ x' := by grind [vars]
      simp only [rename, subst, hyx, reduceIte, fv, hyx', Finset.mem_singleton, not_false_eq_true]
      exact AlphaEquiv.abs_congr (ih (by simp_all [vars]))

/-- Substituting an atom that is fresh for `m` is, up to `∼p`, swapping it with the substituted
atom. This is the first ingredient of Lemma 6.5 [Crole2012]. -/
lemma subst_var_alphaEquiv_swap {m : Term Var} {a a' : Var} (ha' : a' ∉ m.fv) :
    (m[a := var a']) =α (m.swap a a') := by
  -- Rename the bound occurrences of `a'` away (Lemma 6.6), then apply Lemma 6.3.
  obtain ⟨n, hn, hnm⟩ := alphaEquiv_avoid_var ha'
  have h1 : (m[a := var a']) =α (n[a := var a']) :=
    subst.preserve_AlphaEquiv hnm.symm (AlphaEquiv.refl _)
  have h2 : (n[a := var a']) =α (n.swap a a') := by
    rw [swap_eq_rename_of_notMem_vars hn]
    exact (rename_alphaEquiv_subst_var hn).symm
  exact (h1.trans h2).trans (AlphaEquiv.swap_preserve hnm)

/-- If `z` and `a'` are fresh for `m`, then `(z a)` and `(z a') ∘ (a a')` agree on the free atoms
of `m`, so they act alike up to `∼p` by Lemma 6.2(2). This is the second ingredient of
Lemma 6.5 [Crole2012]. -/
lemma swap_alphaEquiv_swap_swap {m : Term Var} {z a a' : Var}
    (hz : z ∉ m.fv) (ha' : a' ∉ m.fv) :
    (m.swap z a) =α ((m.swap a a').swap z a') := by
  simp only [swap, permute_permute]
  apply permute_alphaEquiv_of_eqOn_fv
  intro x hx
  simp only [Equiv.trans_apply, Equiv.swap_apply_def]
  grind

/-- `swapChain [(z₁, a₁, a'₁), ..., (zₙ, aₙ, a'ₙ)] m` is `(z₁ a₁) · ... · (zₙ aₙ) · m`; the head
of the list carries the outermost swap. -/
def swapChain : List (Var × Var × Var) → Term Var → Term Var
  | [], m => m
  | (z, a, _) :: L, m => (swapChain L m).swap z a

/-- `substSwapChain [(z₁, a₁, a'₁), ..., (zₙ, aₙ, a'ₙ)] m` is
`(z₁ a'₁) · ... · (zₙ a'ₙ) · m[a₁ := a'₁] ... [aₙ := a'ₙ]`; the head of the list carries the
outermost swap and the innermost substitution. -/
def substSwapChain : List (Var × Var × Var) → Term Var → Term Var
  | [], m => m
  | (z, a, a') :: L, m => (substSwapChain L (m.subst a (var a'))).swap z a'

/-- The atoms mentioned by a list of triples. -/
def chainAtoms (L : List (Var × Var × Var)) : List Var :=
  L.flatMap fun t => [t.1, t.2.1, t.2.2]

omit [DecidableEq Var] [HasFresh Var] in
/-- Every component of a triple in the list is one of the atoms of the list. -/
lemma mem_chainAtoms {L : List (Var × Var × Var)} {t : Var × Var × Var} (ht : t ∈ L) :
    t.1 ∈ chainAtoms L ∧ t.2.1 ∈ chainAtoms L ∧ t.2.2 ∈ chainAtoms L := by
  split_ands <;> exact List.mem_flatMap.mpr ⟨t, ht, by simp⟩

/-- Chains of swaps preserve `∼p` (Lemma 6.1, iterated). -/
lemma swapChain_congr (L : List (Var × Var × Var)) {m n : Term Var} (h : m =α n) :
    (swapChain L m) =α (swapChain L n) := by
  induction L with
  | nil => exact h
  | cons t T ih => exact AlphaEquiv.swap_preserve ih

/-- Chains of substitutions followed by swaps preserve `∼p`. -/
lemma substSwapChain_congr (L : List (Var × Var × Var)) {m n : Term Var} (h : m =α n) :
    (substSwapChain L m) =α (substSwapChain L n) := by
  induction L generalizing m n with
  | nil => exact h
  | cons t T ih =>
    exact AlphaEquiv.swap_preserve (ih (subst.preserve_AlphaEquiv h (AlphaEquiv.refl _)))

omit [HasFresh Var] in
/-- Two transpositions with disjoint supports commute in their action on terms. -/
lemma swap_swap_comm {m : Term Var} {z a u v : Var}
    (huz : u ≠ z) (hua : u ≠ a) (hvz : v ≠ z) (hva : v ≠ a) :
    (m.swap z a).swap u v = (m.swap u v).swap z a := by
  simp only [swap, permute_permute]
  congr 1
  ext x
  simp only [Equiv.trans_apply, Equiv.swap_apply_def]
  grind

omit [HasFresh Var] in
/-- A swap of atoms that the chain does not mention can be pushed through the chain. -/
lemma swapChain_swap_comm {u v : Var} (L : List (Var × Var × Var)) (m : Term Var)
    (hu : u ∉ chainAtoms L) (hv : v ∉ chainAtoms L) :
    (swapChain L m).swap u v = swapChain L (m.swap u v) := by
  induction L with
  | nil => rfl
  | cons t T ih =>
    obtain ⟨z, a, a'⟩ := t
    simp only [chainAtoms, List.flatMap_cons, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hu hv
    change ((swapChain T m).swap z a).swap u v = (swapChain T (m.swap u v)).swap z a
    rw [swap_swap_comm hu.1.1 hu.1.2.1 hv.1.1 hv.1.2.1, ih hu.2 hv.2]

/-- **Lemma 6.5** [Crole2012]: `(z₁ a₁) ⋯ (zₙ aₙ) · m ∼p (z₁ a'₁) ⋯ (zₙ a'ₙ) · m[a₁ := a'₁] ⋯
[aₙ := a'ₙ]`, for pairwise distinct atoms with `zᵢ` and `a'ᵢ` fresh for `m`.

Crole assumes that the `zᵢ` do not occur in `m`; freshness suffices, because the proof only uses
facts that are invariant under `∼p` and mention free atoms only, and a bound occurrence of `zᵢ`
can be renamed away first (Lemma 6.6). -/
theorem alphaEquiv_swapChain (L : List (Var × Var × Var)) (m : Term Var)
    (hnd : (chainAtoms L).Nodup) (hz : ∀ t ∈ L, t.1 ∉ m.fv) (ha' : ∀ t ∈ L, t.2.2 ∉ m.fv) :
    (swapChain L m) =α (substSwapChain L m) := by
  induction L generalizing m with
  | nil => exact AlphaEquiv.refl _
  | cons t T ih =>
    obtain ⟨z, a, a'⟩ := t
    have hconv : chainAtoms ((z, a, a') :: T) = z :: a :: a' :: chainAtoms T :=
      List.toList_toArray
    rw [hconv] at hnd
    simp only [List.nodup_cons, List.mem_cons] at hnd
    obtain ⟨h1, h2, h3, hndT⟩ := hnd
    have hzT : z ∉ chainAtoms T := by simp_all
    have haT : a ∉ chainAtoms T := by simp_all
    have hzm : z ∉ m.fv := hz (z, a, a') (by simp)
    have ha'm : a' ∉ m.fv := ha' (z, a, a') (by simp)
    -- The head substitution is a swap, up to `∼p`.
    have hsub : (m[a := var a']) =α (m.swap a a') := subst_var_alphaEquiv_swap ha'm
    -- The remaining atoms are still fresh for the swapped term, so the induction hypothesis
    -- applies to it.
    have hIH : (swapChain T (m.swap a a')) =α (substSwapChain T (m.swap a a')) := by
      apply ih (m.swap a a') hndT
      · intro s hs
        have := (mem_chainAtoms hs).1
        exact notMem_fv_swap (by grind) (by grind) (hz s (List.mem_cons_of_mem _ hs))
      · intro s hs
        have := (mem_chainAtoms hs).2.2
        exact notMem_fv_swap (by grind) (by grind) (ha' s (List.mem_cons_of_mem _ hs))
    -- Both head swaps commute past the rest of the chain, and between them sits the
    -- permutation identity `(z a) = (z a') ∘ (a a')` on the free atoms of `m`.
    have core : (swapChain T (m.swap z a)) =α (swapChain T ((m.swap a a').swap z a')) :=
      swapChain_congr T (swap_alphaEquiv_swap_swap hzm ha'm)
    have tail : ((swapChain T (m.swap a a')).swap z a')
        =α ((substSwapChain T (m[a := var a'])).swap z a') :=
      (AlphaEquiv.swap_preserve hIH).trans
        (AlphaEquiv.swap_preserve (substSwapChain_congr T hsub.symm))
    change ((swapChain T m).swap z a) =α ((substSwapChain T (m[a := var a'])).swap z a')
    rw [swapChain_swap_comm T m hzT haT]
    rw [swapChain_swap_comm T _ hzT h3] at tail
    exact core.trans tail

/-- The case `n = 1` of Lemma 6.5 [Crole2012]. This is the step that Crole carries out inside the
proof of Theorem 4.4 for the rule `α`; here it serves Theorems 4.4 and 4.5 alike. -/
lemma alphaEquiv_swap_subst_var {m : Term Var} {z a a' : Var}
    (hz : z ∉ m.vars) (hza : z ≠ a) (haa' : a ≠ a') (ha' : a' ∉ m.fv) :
    (m.swap z a) =α ((m[a := var a']).swap z a') := by
  obtain rfl | hza' := eq_or_ne z a'
  · -- The swap on the right is the identity, and only the first ingredient is left.
    rw [swap_self, swap_comm]
    exact (subst_var_alphaEquiv_swap ha').symm
  · exact alphaEquiv_swapChain [(z, a, a')] m
      (by simp [chainAtoms, hza, haa', hza']) (by simp_all [vars_eq_fv_union_bv])
      (by simpa using ha')

end LambdaCalculus.Named.Untyped.Term

end Cslib
