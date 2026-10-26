/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaQuotient
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivVariants.Swap
public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.DeBruijnPerm
public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.LiftingPermutation

/-! # The bijection between `Λα` and `dB` (paper, Section 4.2)

Theorems 11 and 12 of [Norrish2007a]: the bijection `f : Λα → dB`, and `f` turns `→β` on `Λα`
into `→d'` on `dB`.

## Main definitions

* `Lam` : the raw named syntax `Λvar` over `Atom`, with the `HasFresh Atom` instance.
* `fromTerm` : the map `f` of equation (5) on raw terms.
* `toDB` : the induced map `f : Λα → dB`.
* `dbEquiv` : `f` as an equivalence `Λα ≃ dB` (Theorem 11).

## Main statements

* `fromTerm_dsub` : `f (M[v := N]) = sub (f N) v̂ (f M)` (HOL `fromTerm_subst`), the substitution
  lemma on which Theorem 12 rests.
* `fromTerm_alphaEquiv_iff` : `f M = f N ↔ M =α N` (injectivity, HOL `fromTerm_11`).
* `fromTerm_surjective` : surjectivity, by complete induction on the size of the de Bruijn term
  (HOL `fromTerm_onto`).
* `dbEquiv` : **Theorem 11**, the bijection `Λα ≃ dB`.
* `betaAlpha_iff_dbeta'` : **Theorem 12**, `M →β N ⇔ f M →d' f N` (HOL `dbeta'_eq_ccbeta`).

## Implementation notes

The paper's map `f : Λα → dB` is characterised by the equations (5)

```
f (VAR v)   = dV v̂
f (APP M N) = dAPP (f M) (f N)
f (LAM v M) = dLAM v̂ (f M)
```

The paper obtains `f` from Pitts' α-structural recursion principle [Pitts2006]. Here `fromTerm`
is defined by structural recursion on raw terms, where the equations (5) hold by definition;
`fromTerm_respects_alpha` shows that it respects `=α` (using `dLAM_rename_eq`, which rests on
Theorem 10), and `toDB` is the induced map on `Λα`.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do
  Work*][Norrish2007a]
* [Andrew M. Pitts, *Alpha-structural recursion and induction*][Pitts2006]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.Named.Untyped.Term

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

omit [HasFresh Var] in
/-- A free variable is a variable. -/
lemma mem_vars_of_mem_fv {n : Term Var} {a : Var} (h : a ∈ n.fv) : a ∈ n.vars := by
  grind [vars_eq_fv_union_bv]

/-- Abstracting a term over `y` is α-equivalent to abstracting the swapped term over a variable
`x` that is not free in it. This is the named analogue of the second disjunct of
`Term.dLAM_eq_dLAM_iff`. -/
lemma abs_swap_alphaEquiv {n : Term Var} {x y : Var} (hx : x ∉ n.fv) :
    (Term.abs y n) =α (Term.abs x (n.swap x y)) := by
  obtain ⟨z, hz⟩ := HasFresh.fresh_exists (n.vars ∪ (n.swap x y).vars ∪ {x, y})
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨⟨hzn, hzs⟩, hzx, hzy⟩ := hz
  refine AlphaEquiv.abs (y := z) (by simp [hzn, hzs, hzx, hzy]) ?_
  rw [← swap_eq_rename_of_notMem_vars hzn, ← swap_eq_rename_of_notMem_vars hzs]
  have h : Set.EqOn (Equiv.swap y z) ((Equiv.swap x y).trans (Equiv.swap x z)) n.fv :=
    fun a ha => by grind [mem_vars_of_mem_fv]
  have h' := permute_alphaEquiv_of_eqOn_fv n _ _ h
  rwa [permute_swap, ← permute_permute, permute_swap, permute_swap] at h'

end Cslib.LambdaCalculus.Named.Untyped.Term

namespace Cslib.LambdaCalculus.NamedDeBruijn

open Cslib.Logic.Nominal
open Cslib.LambdaCalculus.Unscoped.Untyped
open Cslib.LambdaCalculus.Named.Untyped (TermAlpha BetaAlpha EtaAlpha)
open Cslib.LambdaCalculus.Named.Untyped.Term (AlphaEquiv)
open scoped Cslib.LambdaCalculus.Named.Untyped Cslib.LambdaCalculus.Named.Untyped.TermAlpha

/-- Atoms have a computable fresh-name generator, so they can be used as the variables of the
named λ-calculus. Atoms are wrapped natural numbers, which also gives the bijection between
"strings" and numbers that the paper needs (`Atom.ofNat` and `Atom.val`). -/
instance : HasFresh Atom := .ofSucc (fun a => ⟨a.val + 1⟩) (fun a => by
  change a.val < a.val + 1
  omega)

/-- `Λvar` over atoms: the raw named syntax of equation (1) [Norrish2007a]. -/
abbrev Lam := Cslib.LambdaCalculus.Named.Untyped.Term Atom

/-- The map `f` of equation (5) [Norrish2007a], by structural recursion on the raw syntax, so
that the equations (5) hold by definition. -/
def fromTerm : Lam → Term
  | .var x => .var x.val
  | .app m n => .app (fromTerm m) (fromTerm n)
  | .abs x m => Term.dLAM x.val (fromTerm m)

/-- Equation (5), variable case. -/
@[simp] lemma fromTerm_var (x : Atom) : fromTerm (.var x) = .var x.val := rfl

/-- Equation (5), application case. -/
lemma fromTerm_app (m n : Lam) :
    fromTerm (.app m n) = .app (fromTerm m) (fromTerm n) := rfl

/-- Equation (5), abstraction case. -/
lemma fromTerm_abs (x : Atom) (m : Lam) :
    fromTerm (.abs x m) = Term.dLAM x.val (fromTerm m) := rfl

/-- `f` is equivariant: `f (π · M) = π · f M`. -/
lemma fromTerm_permute (π : FinPerm) (m : Lam) :
    fromTerm (m.permute π.val) = π • fromTerm m := by
  induction m with
  | var x => rfl
  | app m n ihm ihn => exact congrArg₂ Term.app ihm ihn
  | abs x m ih =>
      change Term.dLAM (π.val x).val (fromTerm (m.permute π.val)) = _
      rw [ih, fromTerm_abs, Term.dpm_dLAM]
      rfl

/-- The special case of `fromTerm_permute` for transpositions. -/
private lemma fromTerm_swap (a b : Atom) (m : Lam) :
    fromTerm (m.swap a b) = (FinPerm.swap a b) • fromTerm m := by
  rw [← Named.Untyped.Term.permute_swap, ← fromTerm_permute]
  rfl

/-- The free indices of `f M` are the codes of the free variables of `M` (membership form of
HOL `dFVs_fromTerm`). -/
lemma mem_dFV_fromTerm (m : Lam) (k : ℕ) :
    k ∈ Term.dFV (fromTerm m) ↔ Atom.ofNat k ∈ m.fv := by
  induction m with
  | var x =>
      change (k ∈ Term.dFV (Term.var x.val)) ↔ _
      simp only [Term.mem_dFV_var, Named.Untyped.Term.fv, Finset.mem_singleton]
      grind [Atom.ext_iff, Atom.ofNat_val]
  | app m n ihm ihn =>
      change (k ∈ Term.dFV (Term.app _ _)) ↔ _
      simp only [Term.mem_dFV_app, ihm, ihn, Named.Untyped.Term.fv, Finset.mem_union]
  | abs x m ih =>
      simp only [fromTerm_abs, Term.dFV_dLAM, Finset.mem_erase, ih,
        Named.Untyped.Term.fv, Finset.mem_sdiff, Finset.mem_singleton]
      grind [Atom.ext_iff, Atom.ofNat_val]

/-- Renaming the abstracted variable by a transposition: if `x` is not free in `M`, then
`dLAM x̂ (f ((x y) · M)) = dLAM ŷ (f M)`, the image under `f` of `LAM x ((x y) · M) = LAM y M`. -/
private lemma dLAM_swap_eq (m : Lam) (x y : Atom) (hx : x ∉ m.fv) :
    Term.dLAM x.val (fromTerm (m.swap x y)) = Term.dLAM y.val (fromTerm m) := by
  have hsupp : (FinPerm.swap x y) • Term.dLAM y.val (fromTerm m)
      = Term.dLAM y.val (fromTerm m) := by
    refine Term.supports_dFV _ _ (fun a ha => ?_)
    simp only [Term.dFV_dLAM, Finset.mem_image, Finset.mem_erase] at ha
    obtain ⟨k, ⟨hky, hkm⟩, rfl⟩ := ha
    refine FinPerm.swap_apply_of_ne_of_ne ?_ ?_
    · intro hc
      exact hx (by rw [← hc]; exact (mem_dFV_fromTerm m k).mp hkm)
    · intro hc
      exact hky (congrArg Atom.val hc)
  rw [Term.dpm_dLAM] at hsupp
  rw [fromTerm_swap, ← hsupp, Atom.val_ofNat, FinPerm.swap_apply_right]

/-- The `rename` version of `dLAM_swap_eq`, matching the shape of the `abs` rule of
`AlphaEquiv`. -/
private lemma dLAM_rename_eq (m : Lam) (y z : Atom) (hz : z ∉ m.vars) :
    Term.dLAM z.val (fromTerm (m.rename y z)) = Term.dLAM y.val (fromTerm m) := by
  rw [← Named.Untyped.Term.swap_eq_rename_of_notMem_vars hz, Named.Untyped.Term.swap_comm]
  exact dLAM_swap_eq m z y (fun hc => hz (Named.Untyped.Term.mem_vars_of_mem_fv hc))

/-- The map `f` respects α-equivalence, hence factors through `Λα`. -/
lemma fromTerm_respects_alpha {m n : Lam} (h : m =α n) : fromTerm m = fromTerm n := by
  induction h with
  | var => rfl
  | app _ _ ih1 ih2 => exact congrArg₂ Term.app ih1 ih2
  | @abs y x1 x2 m1 m2 hy _ ih =>
      simp only [Finset.mem_union, not_or] at hy
      change Term.dLAM x1.val (fromTerm m1) = Term.dLAM x2.val (fromTerm m2)
      rw [← dLAM_rename_eq m1 x1 y hy.1.1, ← dLAM_rename_eq m2 x2 y hy.1.2, ih]

/-- Injectivity of `f` (HOL `fromTerm_11`), by structural induction. The `abs` case is exactly
the de Bruijn lemma `Term.dLAM_eq_dLAM_iff` transported along `abs_swap_alphaEquiv`. -/
lemma fromTerm_injective {m n : Lam} (h : fromTerm m = fromTerm n) : m =α n := by
  induction m generalizing n with
  | var x =>
      cases n with
      | var y =>
          simp only [fromTerm_var, Unscoped.Untyped.Term.var.injEq] at h
          rw [Atom.ext h]
          exact AlphaEquiv.var
      | app _ _ => simp [fromTerm] at h
      | abs _ _ => simp [fromTerm, Term.dLAM] at h
  | app m1 m2 ih1 ih2 =>
      cases n with
      | var _ => simp [fromTerm] at h
      | app n1 n2 =>
          simp only [fromTerm_app, Unscoped.Untyped.Term.app.injEq] at h
          exact AlphaEquiv.app (ih1 h.1) (ih2 h.2)
      | abs _ _ => simp [fromTerm, Term.dLAM] at h
  | abs x m ih =>
      cases n with
      | var _ => simp [fromTerm, Term.dLAM] at h
      | app _ _ => simp [fromTerm, Term.dLAM] at h
      | abs y n =>
          simp only [fromTerm_abs] at h
          rcases Term.dLAM_eq_dLAM_iff.mp h with ⟨hxy, hmn⟩ | ⟨_, hx, hmn⟩
          · rw [Atom.ext hxy]
            exact (ih hmn).abs_congr
          · have hxn : x ∉ n.fv := fun hc =>
              hx ((mem_dFV_fromTerm n x.val).mpr (by rwa [Atom.val_ofNat]))
            have hswap : fromTerm m = fromTerm (n.swap x y) := by
              rw [fromTerm_swap, hmn, Atom.val_ofNat, Atom.val_ofNat]
            exact (ih hswap).abs_congr.trans (Named.Untyped.Term.abs_swap_alphaEquiv hxn).symm

/-- `f M = f N ↔ M =α N` (HOL `fromTerm_11`). -/
lemma fromTerm_alphaEquiv_iff {m n : Lam} : fromTerm m = fromTerm n ↔ m =α n :=
  ⟨fromTerm_injective, fromTerm_respects_alpha⟩

/-- HOL `fromTerm_subst`: `f (M[v := N]) = sub (f N) v̂ (f M)`. The paper proves it by
"BVC-compatible" structural induction on `M`; here it is an induction on the size of the raw
term, with a fresh renaming of the bound variable in the abstraction case. -/
lemma fromTerm_dsub (m n : Lam) (x : Atom) :
    fromTerm (m[x := n]) = Term.dsub (fromTerm n) x.val (fromTerm m) := by
  induction m using Named.Untyped.Term.induction_by_sizeOf with
  | step m ih =>
    match m with
    | .var y =>
        obtain rfl | h := eq_or_ne y x
        · simp [Named.Untyped.Term.subst, Term.dsub]
        · have h' : y.val ≠ x.val := fun hc => h (Atom.ext hc)
          simp [Named.Untyped.Term.subst, h, Term.dsub, h']
    | .app m₁ m₂ =>
        have e : (Named.Untyped.Term.app m₁ m₂)[x := n]
            = Named.Untyped.Term.app (m₁[x := n]) (m₂[x := n]) := by
          simp [Named.Untyped.Term.subst]
        rw [e, fromTerm_app, ih m₁ (by simp +arith), ih m₂ (by simp)]
        rfl
    | .abs y m' =>
        obtain ⟨z, hz⟩ := HasFresh.fresh_exists (m'.vars ∪ n.vars ∪ {x, y})
        have halpha := Named.Untyped.Term.subst.abs_fresh (m := m') (r := n)
          (x := x) (y := y) (z := z) hz
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
        obtain ⟨⟨hzm, hzn⟩, hzx, _⟩ := hz
        have hzdfv : z.val ∉ Term.dFV (fromTerm n) := fun hc =>
          hzn (Named.Untyped.Term.mem_vars_of_mem_fv ((mem_dFV_fromTerm n z.val).mp hc))
        rw [fromTerm_respects_alpha halpha]
        change Term.dLAM z.val (fromTerm ((m'.rename y z)[x := n])) = _
        rw [ih (m'.rename y z) (by simp), ← Term.dsub_dLAM (fun hc => hzx (Atom.ext hc)) hzdfv,
          dLAM_rename_eq m' y z hzm]
        rfl

/-- Surjectivity of `f` (HOL `fromTerm_onto`), by complete induction on `Term.dbsize`. The
`abs` case uses Lemma 6 (`Term.dABS_renamed`). -/
lemma fromTerm_surjective (t : Term) : ∃ m : Lam, fromTerm m = t := by
  suffices h : ∀ k : ℕ, ∀ t : Term, Term.dbsize t ≤ k → ∃ m : Lam, fromTerm m = t by
    exact h (Term.dbsize t) t le_rfl
  intro k
  induction k with
  | zero =>
      intro t ht
      exact absurd ht (by cases t <;> simp [Term.dbsize])
  | succ k ih =>
      intro t ht
      match t with
      | .var i => exact ⟨.var (Atom.ofNat i), rfl⟩
      | .app t u =>
          simp only [Term.dbsize_app] at ht
          obtain ⟨m, hm⟩ := ih t (by omega)
          obtain ⟨n, hn⟩ := ih u (by omega)
          exact ⟨.app m n, by rw [fromTerm_app, hm, hn]⟩
      | .abs t =>
          obtain ⟨i, hi⟩ := Term.dfresh_exists (Term.abs t)
          obtain ⟨t₀, ht₀⟩ := Term.dABS_renamed hi
          have hsize : Term.dbsize t₀ = Term.dbsize t := by
            have h := congrArg Term.dbsize ht₀
            simp only [Term.dbsize_abs, Term.dbsize_dLAM] at h
            omega
          simp only [Term.dbsize_abs] at ht
          obtain ⟨m₀, hm₀⟩ := ih t₀ (by omega)
          exact ⟨.abs (Atom.ofNat i) m₀, by
            change Term.dLAM (Atom.ofNat i).val (fromTerm m₀) = _
            rw [hm₀, Atom.val_ofNat, ← ht₀]⟩

/-- Applying a transposition twice is the identity. -/
private lemma swap_apply_swap_apply (a b c : Atom) :
    (FinPerm.swap a b) ((FinPerm.swap a b) c) = c := by
  rw [← FinPerm.mul_apply, FinPerm.swap_swap]
  rfl

/-- If `f M` is an application, so is `M`. -/
private lemma fromTerm_eq_app {m : Lam} {d₁ d₂ : Term} (h : fromTerm m = Term.app d₁ d₂) :
    ∃ m₁ m₂ : Lam, m = .app m₁ m₂ ∧ fromTerm m₁ = d₁ ∧ fromTerm m₂ = d₂ := by
  match m with
  | .var x => simp [fromTerm] at h
  | .abs x m => simp [fromTerm, Term.dLAM] at h
  | .app m₁ m₂ =>
      change Term.app (fromTerm m₁) (fromTerm m₂) = _ at h
      simp only [Unscoped.Untyped.Term.app.injEq] at h
      exact ⟨m₁, m₂, rfl, h.1, h.2⟩

/-- If `f M` is a `dLAM`-abstraction over `i`, then `M` is α-equivalent to an abstraction
over `î`.  The "swapped" branch of `Term.dLAM_eq_dLAM_iff` is matched by
`abs_swap_alphaEquiv` on the named side. -/
private lemma fromTerm_eq_dLAM {m : Lam} {i : ℕ} {d : Term} (h : fromTerm m = Term.dLAM i d) :
    ∃ m₀ : Lam, m =α (.abs (Atom.ofNat i) m₀) ∧ fromTerm m₀ = d := by
  match m with
  | .var x => simp [fromTerm, Term.dLAM] at h
  | .app m₁ m₂ => simp [fromTerm, Term.dLAM] at h
  | .abs y m' =>
      change Term.dLAM y.val (fromTerm m') = _ at h
      rcases Term.dLAM_eq_dLAM_iff.mp h with ⟨hy, hd⟩ | ⟨_, hy, hd⟩
      · obtain rfl : y = Atom.ofNat i := Atom.ext hy
        exact ⟨m', AlphaEquiv.refl _, hd⟩
      · refine ⟨m'.swap (Atom.ofNat i) y, ?_, ?_⟩
        · have hifv : Atom.ofNat i ∉ m'.fv := by
            intro hc
            have hmem : i ∈ Term.dFV (fromTerm m') := (mem_dFV_fromTerm m' i).mpr hc
            rw [hd, Term.mem_dFV_dpm] at hmem
            obtain ⟨k, hk, hik⟩ := hmem
            have h1 : (FinPerm.swap (Atom.ofNat y.val) (Atom.ofNat i)) (Atom.ofNat k)
                = Atom.ofNat i := Atom.ext hik
            have h3 := swap_apply_swap_apply (Atom.ofNat y.val) (Atom.ofNat i) (Atom.ofNat k)
            rw [h1, FinPerm.swap_apply_right] at h3
            exact hy (by rw [show y.val = k from congrArg Atom.val h3]; exact hk)
          exact Named.Untyped.Term.abs_swap_alphaEquiv hifv
        · rw [fromTerm_swap, hd, ← mul_smul, Atom.val_ofNat y,
            FinPerm.swap_comm (Atom.ofNat i) y, FinPerm.swap_swap, one_smul]

/-- The map `f : Λα → dB` of equation (5). -/
def toDB : TermAlpha Atom → Term :=
  Quotient.lift fromTerm (fun _ _ h => fromTerm_respects_alpha h)

/-- `f` on the class of a raw term is `fromTerm` of that term. -/
@[simp] lemma toDB_mk (m : Lam) : toDB ⟦m⟧α = fromTerm m := rfl

/-- Equation (5) on `Λα`, variable case. -/
@[simp] lemma toDB_var (x : Atom) : toDB (TermAlpha.var x) = .var x.val := rfl

/-- Equation (5) on `Λα`, application case. -/
@[simp] lemma toDB_app (M N : TermAlpha Atom) :
    toDB (TermAlpha.app M N) = .app (toDB M) (toDB N) := by
  induction M using TermAlpha.ind
  induction N using TermAlpha.ind
  rfl

/-- Equation (5) on `Λα`, abstraction case. -/
@[simp] lemma toDB_abs (x : Atom) (M : TermAlpha Atom) :
    toDB (TermAlpha.abs x M) = Term.dLAM x.val (toDB M) := by
  induction M using TermAlpha.ind
  rfl

/-- **Theorem 11** [Norrish2007a] (`dB` is in bijection with `Λα`): there exists a bijective
`f : Λα → dB` with defining equations as in (5). -/
noncomputable def dbEquiv : TermAlpha Atom ≃ Term where
  toFun := toDB
  invFun t := ⟦(fromTerm_surjective t).choose⟧α
  left_inv := by
    intro M
    induction M using TermAlpha.ind with
    | _ m =>
      exact TermAlpha.mk_eq_mk.mpr
        (fromTerm_alphaEquiv_iff.mp (fromTerm_surjective (fromTerm m)).choose_spec)
  right_inv := fun t => (fromTerm_surjective t).choose_spec

/-- `f` is injective on `Λα` (the injectivity half of Theorem 11). -/
lemma toDB_injective : Function.Injective toDB := by
  intro M N h
  induction M using TermAlpha.ind with
  | _ m =>
    induction N using TermAlpha.ind with
    | _ n => exact TermAlpha.mk_eq_mk.mpr (fromTerm_alphaEquiv_iff.mp h)

/-- The quotient-level form of `fromTerm_dsub`. -/
lemma toDB_subst (M N : TermAlpha Atom) (x : Atom) :
    toDB (TermAlpha.subst M x N) = Term.dsub (toDB N) x.val (toDB M) := by
  induction M using TermAlpha.ind with
  | _ m =>
    induction N using TermAlpha.ind with
    | _ n => exact fromTerm_dsub m n x

/-- Inversion of `f` at an application, on `Λα`. -/
lemma toDB_eq_app {M : TermAlpha Atom} {d₁ d₂ : Term} (h : toDB M = Term.app d₁ d₂) :
    ∃ M₁ M₂ : TermAlpha Atom, M = TermAlpha.app M₁ M₂ ∧ toDB M₁ = d₁ ∧ toDB M₂ = d₂ := by
  induction M using TermAlpha.ind with
  | _ m =>
    obtain ⟨m₁, m₂, hm, h₁, h₂⟩ := fromTerm_eq_app h
    exact ⟨⟦m₁⟧α, ⟦m₂⟧α, by rw [hm]; rfl, h₁, h₂⟩

/-- Inversion of `f` at an abstraction, on `Λα`. -/
lemma toDB_eq_dLAM {M : TermAlpha Atom} {i : ℕ} {d : Term} (h : toDB M = Term.dLAM i d) :
    ∃ M₀ : TermAlpha Atom, M = TermAlpha.abs (Atom.ofNat i) M₀ ∧ toDB M₀ = d := by
  induction M using TermAlpha.ind with
  | _ m =>
    obtain ⟨m₀, halpha, h₀⟩ := fromTerm_eq_dLAM h
    exact ⟨⟦m₀⟧α, TermAlpha.mk_eq_mk.mpr halpha, h₀⟩

/-- The "→" half of Theorem 12: a rule induction on `→βα`; the contraction case is exactly
`fromTerm_dsub`. -/
lemma dbeta'_of_betaAlpha {M N : TermAlpha Atom} (h : M →βα N) : toDB M →d' toDB N := by
  induction h with
  | red x M N => simpa [toDB_subst] using DBeta'.red x.val (toDB M) (toDB N)
  | appL Z _ ih => simpa using DBeta'.appL (toDB Z) ih
  | appR Z _ ih => simpa using DBeta'.appR (toDB Z) ih
  | abs x _ ih => simpa using DBeta'.lam x.val ih

/-- The "←" half of Theorem 12: a rule induction on `→d'`, using the inversion lemmas for `f`. -/
lemma betaAlpha_of_dbeta' {t u : Term} (h : t →d' u) (M N : TermAlpha Atom) (hM : toDB M = t)
    (hN : toDB N = u) : M →βα N := by
  induction h generalizing M N with
  | red i t u =>
      obtain ⟨M₁, M₂, rfl, h₁, h₂⟩ := toDB_eq_app hM
      obtain ⟨M₀, rfl, h₀⟩ := toDB_eq_dLAM h₁
      have hsub : N = TermAlpha.subst M₀ (Atom.ofNat i) M₂ := by
        refine toDB_injective ?_
        rw [hN, toDB_subst, h₀, h₂]
        rfl
      rw [hsub]
      exact BetaAlpha.red _ _ _
  | appL z _ ih =>
      obtain ⟨M₁, M₂, rfl, h₁, h₂⟩ := toDB_eq_app hM
      obtain ⟨N₁, N₂, rfl, k₁, k₂⟩ := toDB_eq_app hN
      rw [show M₂ = N₂ from toDB_injective (by rw [h₂, k₂])]
      exact BetaAlpha.appL _ (ih M₁ N₁ h₁ k₁)
  | appR z _ ih =>
      obtain ⟨M₁, M₂, rfl, h₁, h₂⟩ := toDB_eq_app hM
      obtain ⟨N₁, N₂, rfl, k₁, k₂⟩ := toDB_eq_app hN
      rw [show M₁ = N₁ from toDB_injective (by rw [h₁, k₁])]
      exact BetaAlpha.appR _ (ih M₂ N₂ h₂ k₂)
  | lam i _ ih =>
      obtain ⟨M₀, rfl, h₀⟩ := toDB_eq_dLAM hM
      obtain ⟨N₀, rfl, k₀⟩ := toDB_eq_dLAM hN
      exact BetaAlpha.abs _ (ih M₀ N₀ h₀ k₀)

/-- **Theorem 12** [Norrish2007a]: `M →β N ⇔ f M →d' f N`. -/
theorem betaAlpha_iff_dbeta' {M N : TermAlpha Atom} : M →βα N ↔ toDB M →d' toDB N :=
  ⟨dbeta'_of_betaAlpha, fun h => betaAlpha_of_dbeta' h M N rfl rfl⟩

end Cslib.LambdaCalculus.NamedDeBruijn
