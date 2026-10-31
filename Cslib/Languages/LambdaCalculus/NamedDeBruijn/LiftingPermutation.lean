/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.DeBruijnPerm

/-! # Lifting is a permutation

The first half of Section 4.3 of [Norrish2007a]: inside `dLAM`, lifting acts as a permutation,
so an equivariant relation cannot tell a `dABS` term from its `dLAM` presentation.

## Main statements

* `Term.dsub_eq_nsub` : **Lemma 13**.
* `Term.lift_eq_dpm` : **Lemma 14**.
* `Term.dABS_rules_are_dLAM_compatible` : **Theorem 15**.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do
  Work*][Norrish2007a]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.Unscoped.Untyped

open Cslib.Logic.Nominal

namespace Term

/-- **Lemma 13** (HOL `sub_nsub`): for `n ≤ i`,
`sub u i t = nsub u n (sub (dV n) (i+1) (lift t n))`. -/
lemma dsub_eq_nsub (u : Term) (i n : ℕ) (t : Term) (h : n ≤ i) :
    dsub u i t = nsub u n (dsub (var n) (i + 1) (lift t n)) := by
  induction t generalizing u i n with
  | var m =>
      simp only [lift_var]
      split_ifs <;> simp only [dsub_var] <;> split_ifs <;> simp only [nsub_var] <;>
        split_ifs <;> first | rfl | (congr 1; omega)
  | app t₁ t₂ ih₁ ih₂ =>
      simp only [lift_app, dsub_app, nsub_app, ih₁ u i n h, ih₂ u i n h]
  | abs t ih =>
      simp only [lift_abs, dsub_abs, nsub_abs, lift_var, Nat.not_lt_zero, ite_false]
      exact congrArg abs (ih (lift u 0) (i + 1) (n + 1) (by omega))

/-- Nipkow's relation `→d` does reduce `→d'`-redexes in the correct way (HOL `alt_dbeta_rule`):
`dAPP (dLAM i t) u →d sub u i t`. Lemma 13 with `n = 0`. -/
lemma beta_dLAM_redex (i : ℕ) (t u : Term) : app (dLAM i t) u ⭢β dsub u i t := by
  rw [dsub_eq_nsub u i 0 t (Nat.zero_le i)]
  exact Beta.red _ _

/-- Conversely, the de Bruijn redexes reduce under `→d'` (HOL `alt_dbeta'_rule`):
`dAPP (dABS t) u →d' nsub u 0 t`. -/
lemma dbeta'_dABS_redex (t u : Term) : app (abs t) u →d' nsub u 0 t := by
  obtain ⟨i, hi⟩ := dfresh_exists (abs t)
  obtain ⟨t₀, ht⟩ := dABS_renamed hi
  have ht' : t = dsub (var 0) (i + 1) (lift t₀ 0) := Term.abs.inj ht
  rw [ht, ht', ← dsub_eq_nsub u i 0 t₀ (Nat.zero_le i)]
  exact DBeta'.red i t₀ u

/-- The function underlying `liftingPerm lim n`: it maps `î` to `i+1` for `lim ≤ i ≤ n`, maps
`n+1` back to `lim`, and fixes all other atoms (HOL `lifting_pm_behaves`). -/
def liftingPermFun (lim n : ℕ) (a : Atom) : Atom :=
  if a.val < lim then a
  else if a.val ≤ n then ⟨a.val + 1⟩
  else if a.val = n + 1 then ⟨lim⟩
  else a

/-- The inverse of `liftingPermFun lim n`. -/
def liftingPermInvFun (lim n : ℕ) (a : Atom) : Atom :=
  if a.val < lim then a
  else if a.val = lim then (if lim ≤ n then ⟨n + 1⟩ else a)
  else if a.val ≤ n + 1 then ⟨a.val - 1⟩
  else a

/-- `liftingPermInvFun lim n` is a right inverse of `liftingPermFun lim n`. -/
lemma liftingPermFun_inv (lim n : ℕ) (a : Atom) :
    liftingPermFun lim n (liftingPermInvFun lim n a) = a := by
  obtain ⟨v⟩ := a
  simp only [liftingPermFun, liftingPermInvFun]
  split_ifs <;> grind

/-- `liftingPermInvFun lim n` is a left inverse of `liftingPermFun lim n`. -/
lemma liftingPermInvFun_inv (lim n : ℕ) (a : Atom) :
    liftingPermInvFun lim n (liftingPermFun lim n a) = a := by
  obtain ⟨v⟩ := a
  simp only [liftingPermFun, liftingPermInvFun]
  split_ifs <;> grind

/-- The lifting permutation `lift-pm(lim, n)` (HOL `lifting_pm_def`), the cycle
`lim → lim+1 → ... → n+1 → lim` on atoms. -/
def liftingPerm (lim n : ℕ) : FinPerm :=
  ⟨⟨liftingPermFun lim n, liftingPermInvFun lim n,
      fun a => liftingPermInvFun_inv lim n a, fun a => liftingPermFun_inv lim n a⟩,
    (Finset.range (n + 2)).image (fun i => (⟨i⟩ : Atom)), by
      intro a ha
      simp only [Finset.mem_image, Finset.mem_range, not_exists] at ha
      have hlarge : ¬ a.val < n + 2 := fun h => ha a.val ⟨h, rfl⟩
      change liftingPermFun lim n a = a
      simp only [liftingPermFun]
      split_ifs <;> first | rfl | (exfalso; omega)⟩

/-- HOL `lifting_pm_behaves`: the characterisation of the lifting permutation. -/
lemma liftingPerm_apply (lim n i : ℕ) :
    liftingPerm lim n (Atom.ofNat i) =
      if i < lim then Atom.ofNat i
      else if i ≤ n then Atom.ofNat (i + 1)
      else if i = n + 1 then Atom.ofNat lim
      else Atom.ofNat i := rfl

/-- The `dABS` case of Lemma 14 (HOL `inc_pm0_lifting_pm`):
`inc 0 (lifting_pm (m, n)) = lifting_pm (m+1, n+1)`. -/
lemma incPerm_zero_liftingPerm (m n : ℕ) :
    incPerm 0 (liftingPerm m n) = liftingPerm (m + 1) (n + 1) := by
  refine FinPerm.ext (fun a => ?_)
  simp only [incPerm_apply, incFun, gincAtom, gdecAtom, Nat.not_lt_zero, ite_false,
    Nat.le_zero_eq, show ∀ (b : Atom), liftingPerm m n b = liftingPermFun m n b from fun _ => rfl,
    show ∀ (b : Atom), liftingPerm (m + 1) (n + 1) b = liftingPermFun (m + 1) (n + 1) b from
      fun _ => rfl,
    liftingPermFun]
  split_ifs <;> apply Atom.ext <;> (try dsimp only at *) <;> omega

/-- **Lemma 14** (Lifting is a permutation, HOL `lifts_are_specific_dpms`): if `n` is at least
as large as the largest free index in `t`, then `lift t m = (lifting_pm (m, n)) · t`. -/
lemma lift_eq_dpm (t : Term) (n : ℕ) (h : ∀ i ∈ dFV t, i ≤ n) (m : ℕ) :
    lift t m = (liftingPerm m n) • t := by
  induction t generalizing m n with
  | var i =>
      have hi : i ≤ n := h i (by simp)
      rw [dpm_var, lift_var, liftingPerm_apply]
      simp only [apply_ite Atom.val, Atom.ofNat_val]
      split_ifs <;> rfl
  | app t u iht ihu =>
      rw [dpm_app, lift_app, iht n (fun i hi => h i (by simp [hi])),
        ihu n (fun i hi => h i (by simp [hi]))]
  | abs t ih =>
      rw [dpm_abs, lift_abs, incPerm_zero_liftingPerm]
      refine congrArg abs (ih (n + 1) (fun j hj => ?_) (m + 1))
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · omega
      · have hmem : j - 1 ∈ dFV (abs t) := by
          simp only [mem_dFV_abs]
          rwa [show j - 1 + 1 = j by omega]
        have := h _ hmem
        omega

/-- Incrementing a transposition of indices shifts both indices. -/
lemma incPerm_zero_swap (i j : ℕ) :
    incPerm 0 (FinPerm.swap (Atom.ofNat i) (Atom.ofNat j)) =
      FinPerm.swap (Atom.ofNat (i + 1)) (Atom.ofNat (j + 1)) := by
  refine FinPerm.ext (fun ⟨v⟩ => ?_)
  rw [incPerm_apply]
  simp only [incFun, gincAtom, gdecAtom, FinPerm.apply_def, FinPerm.swap_val,
    Equiv.swap_apply_def, Atom.ofNat]
  split_ifs <;> grind

/-- Substituting `dV i` for `j` in a term in which `i` is not free is the transposition
`[i ↔ j]` (HOL `fresh_dpm_sub`, `dLAM_alt_dpm`). -/
lemma dsub_var_eq_dpm {t : Term} {i j : ℕ} (h : i ∉ dFV t) :
    dsub (var i) j t = (FinPerm.swap (Atom.ofNat i) (Atom.ofNat j)) • t := by
  induction t generalizing i j with
  | var m =>
      simp only [mem_dFV_var] at h
      simp only [dsub_var, dpm_var, FinPerm.apply_def, FinPerm.swap_val, Equiv.swap_apply_def,
        Atom.ofNat]
      split_ifs <;> grind
  | app t u iht ihu =>
      simp only [mem_dFV_app, not_or] at h
      rw [dsub_app, dpm_app, iht h.1, ihu h.2]
  | abs t ih =>
      simp only [mem_dFV_abs] at h
      rw [dsub_abs, dpm_abs, incPerm_zero_swap, lift_var]
      simp only [Nat.not_lt_zero, ite_false]
      exact congrArg abs (ih h)

/-- Lemma 14 and `dsub_var_eq_dpm` together: `dLAM i t` is `dABS` of a permutation of `t` that
depends only on `i` and on a bound `n` for the free indices of `t`. -/
lemma dLAM_eq_abs_dpm (i n : ℕ) (t : Term) (h : ∀ k ∈ dFV t, k ≤ n) :
    dLAM i t =
      abs ((FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1)) * liftingPerm 0 n) • t) := by
  rw [dLAM, dsub_var_eq_dpm (by grind [mem_dFV_lift]), lift_eq_dpm t n h 0, mul_smul]

/-- Lifting is injective (HOL `lift_11`). -/
lemma lift_inj {t u : Term} {n : ℕ} (h : lift t n = lift u n) : t = u := by
  induction t generalizing u n with
  | var m =>
      cases u with
      | var k => simp only [lift_var] at h; split_ifs at h <;> simp_all <;> omega
      | app _ _ => simp only [lift_var, lift_app] at h; split_ifs at h
      | abs _ => simp only [lift_var, lift_abs] at h; split_ifs at h
  | app t₁ t₂ ih₁ ih₂ =>
      cases u with
      | var k => simp only [lift_var, lift_app] at h; split_ifs at h
      | app u₁ u₂ =>
          simp only [lift_app, Term.app.injEq] at h
          exact congr (congrArg _ (ih₁ h.1)) (ih₂ h.2)
      | abs _ => simp only [lift_app, lift_abs] at h; exact absurd h (by simp)
  | abs t ih =>
      cases u with
      | var k => simp only [lift_var, lift_abs] at h; split_ifs at h
      | app _ _ => simp only [lift_app, lift_abs] at h; exact absurd h (by simp)
      | abs u => simp only [lift_abs, Term.abs.injEq] at h; exact congrArg _ (ih h)

/-- Index `0` is never free in a term lifted at `0`. -/
lemma zero_not_mem_dFV_lift (t : Term) : (0 : ℕ) ∉ dFV (lift t 0) := by
  simp only [mem_dFV_lift]
  rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega

/-- The free indices of `lift t 0`, above `0`. -/
lemma mem_dFV_lift_succ (u : Term) (i : ℕ) : i + 1 ∈ dFV (lift u 0) ↔ i ∈ dFV u := by
  simp only [mem_dFV_lift, Nat.add_sub_cancel]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · omega
    · exact h
  · intro h; exact Or.inr ⟨by omega, h⟩

/-- The permutation form of `dLAM`, obtained from `dsub_var_eq_dpm`: the substitution inside
`dLAM` is the transposition `[0 ↔ i+1]`. -/
lemma dLAM_eq_abs_swap (i : ℕ) (t : Term) :
    dLAM i t = abs ((FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1))) • lift t 0) := by
  rw [dLAM, dsub_var_eq_dpm (zero_not_mem_dFV_lift t)]

/-- The permutation action on de Bruijn terms is injective. -/
lemma dpm_left_cancel {π : FinPerm} {t u : Term} (h : π • t = π • u) : t = u := by
  have h' := congrArg (fun x : Term => π⁻¹ • x) h
  simpa only [inv_smul_smul] using h'

/-- The main step of `dLAM_eq_dLAM_iff`: two transposed lifts agree only if the two bodies are
related by the transposition `[i ↔ j]` and `i` is fresh for the second one. -/
lemma swap_lift_eq_aux {i j : ℕ} {t u : Term} (hij : i ≠ j)
    (h : (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1))) • lift t 0
        = (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (j + 1))) • lift u 0) :
    i ∉ dFV u ∧ t = (FinPerm.swap (Atom.ofNat i) (Atom.ofNat j)) • u := by
  set σ := FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1)) with hσ
  set τ := FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (j + 1)) with hτ
  set ρ := FinPerm.swap (Atom.ofNat (i + 1)) (Atom.ofNat (j + 1)) with hρ
  have hA : lift t 0 = (σ * τ) • lift u 0 := by
    rw [mul_smul, ← h, ← mul_smul, show σ * σ = 1 from FinPerm.swap_swap _ _, one_smul]
  have hiB : i + 1 ∉ dFV (lift u 0) := by
    intro hmem
    refine zero_not_mem_dFV_lift t ?_
    rw [hA, mem_dFV_dpm]
    refine ⟨i + 1, hmem, ?_⟩
    rw [hσ, hτ, FinPerm.mul_apply]
    simp only [FinPerm.apply_def, FinPerm.swap_val, Equiv.swap_apply_def, Atom.ofNat]
    split_ifs <;> grind
  refine ⟨fun hc => hiB ((mem_dFV_lift_succ u i).mpr hc), ?_⟩
  have hfix : (ρ⁻¹ * (σ * τ)) • lift u 0 = lift u 0 := by
    refine supports_dFV (lift u 0) _ (fun a ha => ?_)
    simp only [Finset.mem_image] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    have hk0 : k ≠ 0 := fun hc => zero_not_mem_dFV_lift u (hc ▸ hk)
    have hki : k ≠ i + 1 := fun hc => hiB (hc ▸ hk)
    rw [hρ, hσ, hτ, FinPerm.swap_inv, FinPerm.mul_apply, FinPerm.mul_apply]
    simp only [FinPerm.apply_def, FinPerm.swap_val, Equiv.swap_apply_def, Atom.ofNat]
    split_ifs <;> grind
  have hAρ : lift t 0 = ρ • lift u 0 := by
    rw [hA, show σ * τ = ρ * (ρ⁻¹ * (σ * τ)) by rw [← mul_assoc, mul_inv_cancel, one_mul],
      mul_smul, hfix]
  rw [hρ, ← incPerm_zero_swap, ← lift_dpm] at hAρ
  exact lift_inj hAρ

/-- `dLAM` is injective up to a transposition of the two abstracted indices, like `LAM` on
`Λα`. -/
lemma dLAM_eq_dLAM_iff {i j : ℕ} {t u : Term} :
    dLAM i t = dLAM j u ↔
      (i = j ∧ t = u) ∨
        (i ≠ j ∧ i ∉ dFV u ∧ t = (FinPerm.swap (Atom.ofNat i) (Atom.ofNat j)) • u) := by
  constructor
  · intro hEq
    rw [dLAM_eq_abs_swap, dLAM_eq_abs_swap, Term.abs.injEq] at hEq
    rcases eq_or_ne i j with rfl | hij
    · exact Or.inl ⟨rfl, lift_inj (dpm_left_cancel hEq)⟩
    · obtain ⟨h1, h2⟩ := swap_lift_eq_aux hij hEq
      exact Or.inr ⟨hij, h1, h2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hij, hi, rfl⟩)
    · rfl
    · have hsupp : (FinPerm.swap (Atom.ofNat i) (Atom.ofNat j)) • dLAM j u = dLAM j u := by
        refine supports_dFV (dLAM j u) _ (fun a ha => ?_)
        simp only [dFV_dLAM, Finset.mem_image, Finset.mem_erase] at ha
        obtain ⟨k, ⟨hkj, hku⟩, rfl⟩ := ha
        refine FinPerm.swap_apply_of_ne_of_ne ?_ ?_
        · intro hk; exact hi (by rwa [show k = i from congrArg Atom.val hk] at hku)
        · intro hk; exact hkj (congrArg Atom.val hk)
      rwa [dpm_dLAM, FinPerm.swap_apply_right] at hsupp

/-- **Theorem 15** (Abstraction Congruences Correspond): if `R` is equivariant, then the
`dABS`-congruence rule and the `dLAM`-congruence rule for `R` are equivalent
(HOL `dABS_rules_are_dLAM_compatible`). -/
theorem dABS_rules_are_dLAM_compatible (R : Term → Term → Prop)
    (hR : ∀ (π : FinPerm) (t u : Term), R (π • t) (π • u) ↔ R t u) :
    (∀ t u, R t u → R (abs t) (abs u)) ↔ (∀ i t u, R t u → R (dLAM i t) (dLAM i u)) := by
  constructor
  · intro habs i t u htu
    obtain ⟨n, hn⟩ := dFV_bounded (app t u)
    rw [dLAM_eq_abs_dpm i n t (fun k hk => (hn k (by simp [hk])).le),
      dLAM_eq_abs_dpm i n u (fun k hk => (hn k (by simp [hk])).le)]
    exact habs _ _ ((hR _ t u).mpr htu)
  · intro hlam t u htu
    obtain ⟨i, hi⟩ := dfresh_exists (app (abs t) (abs u))
    simp only [mem_dFV_app, not_or] at hi
    obtain ⟨t₀, ht₀⟩ := dABS_renamed hi.1
    obtain ⟨u₀, hu₀⟩ := dABS_renamed hi.2
    obtain ⟨n, hn⟩ := dFV_bounded (app t₀ u₀)
    have ht : ∀ k ∈ dFV t₀, k ≤ n := fun k hk => (hn k (by simp [hk])).le
    have hu : ∀ k ∈ dFV u₀, k ≤ n := fun k hk => (hn k (by simp [hk])).le
    rw [ht₀, hu₀]
    refine hlam i t₀ u₀ ((hR (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1))
      * liftingPerm 0 n) t₀ u₀).mp ?_)
    have e1 : t = (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1)) * liftingPerm 0 n) • t₀ :=
      Term.abs.inj (by rw [ht₀, dLAM_eq_abs_dpm i n t₀ ht])
    have e2 : u = (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1)) * liftingPerm 0 n) • u₀ :=
      Term.abs.inj (by rw [hu₀, dLAM_eq_abs_dpm i n u₀ hu])
    rwa [← e1, ← e2]

end Term

end Cslib.LambdaCalculus.Unscoped.Untyped
