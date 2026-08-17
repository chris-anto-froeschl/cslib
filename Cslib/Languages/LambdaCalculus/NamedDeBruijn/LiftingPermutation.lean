/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.NamedDeBruijn.DeBruijnPerm

/-! # Lifting is a permutation (paper, Section 4.3)

The "nominal *Aha!*" of

* Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*,
  TPHOLs 2007

is that the substitution and the lifting hidden inside `dLAM` are nothing but a variable
permutation.  This file contains the corresponding results:

* **Lemma 13**, relating the paper's clean substitution `sub` to Nipkow's `nsub`, and the two
  "alternative redex rules" that it yields;
* **Lemma 14**, that lifting is the action of the explicitly constructed permutation
  `liftingPerm`;
* **Theorem 15**, that for an equivariant relation the `dABS`- and `dLAM`-congruence rules
  correspond.

## Main statements

* `Term.dsub_eq_nsub` : **Lemma 13**, `n ≤ i → sub u i t = nsub u n (sub (dV n) (i+1) (lift t n))`.
* `Term.beta_dLAM_redex` : Nipkow's `→d` reduces `→d'`-redexes correctly (HOL `alt_dbeta_rule`).
* `Term.dbeta'_dABS_redex` : `→d'` reduces de Bruijn redexes correctly (HOL `alt_dbeta'_rule`).
* `Term.liftingPerm`, `Term.liftingPerm_apply` : the lifting permutation and its behaviour
  (HOL `lifting_pm_def`, `lifting_pm_behaves`).
* `Term.lift_eq_dpm` : **Lemma 14** (HOL `lifts_are_specific_dpms`, `lifts_are_dpms`).
* `Term.dABS_rules_are_dLAM_compatible` : **Theorem 15**.

## References

* [Michael Norrish and René Vestergaard, *Proof Pearl: de Bruijn Terms Really Do Work*][NV2007]
-/

@[expose] public section

namespace Cslib.LambdaCalculus.Unscoped.Untyped

open CatCrypt.Nominal

namespace Term

/-! ### Lemma 13 and the alternative redex rules -/

/-- **Lemma 13** (HOL `sub_nsub`): for `n ≤ i`,
`sub u i t = nsub u n (sub (dV n) (i+1) (lift t n))`.  Proved by structural induction on `t`. -/
theorem dsub_eq_nsub (u : Term) (i n : ℕ) (t : Term) (h : n ≤ i) :
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
`dAPP (dLAM i t) u →d sub u i t`.  Immediate from **Lemma 13** with `n = 0`. -/
theorem beta_dLAM_redex (i : ℕ) (t u : Term) : Beta (app (dLAM i t) u) (dsub u i t) := by
  rw [dsub_eq_nsub u i 0 t (Nat.zero_le i)]
  exact Beta.red _ _

/-- Conversely, the de Bruijn redexes reduce under `→d'` (HOL `alt_dbeta'_rule`):
`dAPP (dABS t) u →d' nsub u 0 t`. -/
theorem dbeta'_dABS_redex (t u : Term) : DBeta' (app (abs t) u) (nsub u 0 t) := by
  obtain ⟨i, hi⟩ := dfresh_exists (abs t)
  obtain ⟨t₀, ht⟩ := dABS_renamed hi
  have ht' : t = dsub (var 0) (i + 1) (lift t₀ 0) := Term.abs.inj ht
  rw [ht, ht', ← dsub_eq_nsub u i 0 t₀ (Nat.zero_le i)]
  exact DBeta'.red i t₀ u

/-! ### Lemma 14 — lifting is a permutation -/

/-- The lifting permutation (HOL `lifting_pm_def`).  Given a lower bound `lim` and an upper
bound `n`, `liftingPerm lim n` is the cycle that maps `î` to `i+1` for `lim ≤ i ≤ n`, maps
`n+1` back to `lim`, and preserves all other values. -/
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

theorem liftingPermFun_inv (lim n : ℕ) (a : Atom) :
    liftingPermFun lim n (liftingPermInvFun lim n a) = a := by
  obtain ⟨v⟩ := a
  simp only [liftingPermFun, liftingPermInvFun]
  split_ifs <;> simp_all <;> omega

theorem liftingPermInvFun_inv (lim n : ℕ) (a : Atom) :
    liftingPermInvFun lim n (liftingPermFun lim n a) = a := by
  obtain ⟨v⟩ := a
  simp only [liftingPermFun, liftingPermInvFun]
  split_ifs <;> simp_all <;> omega

/-- The lifting permutation as an element of `FinPerm`. -/
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
@[simp] theorem liftingPerm_apply (lim n i : ℕ) :
    liftingPerm lim n (Atom.ofNat i) =
      if i < lim then Atom.ofNat i
      else if i ≤ n then Atom.ofNat (i + 1)
      else if i = n + 1 then Atom.ofNat lim
      else Atom.ofNat i := rfl

/-- Another tedious index-manoeuvring result (HOL `inc_pm0_lifting_pm`), needed in the `dABS`
case of **Lemma 14**: `inc 0 (lifting_pm (m, n)) = lifting_pm (m+1, n+1)`.  As the paper notes,
this one thankfully does not need to be generalised to `inc i`. -/
theorem incPerm_zero_liftingPerm (m n : ℕ) :
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
theorem lift_eq_dpm (t : Term) (n : ℕ) (h : ∀ i ∈ dFV t, i ≤ n) (m : ℕ) :
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

/-- **Lemma 14**, existential form (HOL `lifts_are_dpms`): every lifting is a permutation. -/
theorem lift_is_dpm (t : Term) (m : ℕ) : ∃ π : FinPerm, lift t m = π • t := by
  obtain ⟨n, hn⟩ := dFV_bounded t
  exact ⟨liftingPerm m n, lift_eq_dpm t n (fun i hi => (hn i hi).le) m⟩

/-- Incrementing a transposition of indices shifts both indices. -/
theorem incPerm_zero_swap (i j : ℕ) :
    incPerm 0 (FinPerm.swap (Atom.ofNat i) (Atom.ofNat j)) =
      FinPerm.swap (Atom.ofNat (i + 1)) (Atom.ofNat (j + 1)) := by
  refine FinPerm.ext (fun a => ?_)
  apply Atom.ext
  rw [incPerm_apply, show a = Atom.ofNat a.val from rfl, incFun_zero_val]
  rcases Nat.eq_zero_or_pos a.val with h0 | h0
  · rw [ite_eq_left h0, FinPerm.swap_apply_of_ne_of_ne] <;> simp [Atom.ofNat, h0]
  · rw [ite_eq_right (by omega)]
    by_cases hi : a.val - 1 = i
    · rw [hi, FinPerm.swap_apply_left]
      have hv : a.val = i + 1 := by omega
      rw [hv, FinPerm.swap_apply_left]
      rfl
    · by_cases hj : a.val - 1 = j
      · rw [hj, FinPerm.swap_apply_right]
        have hv : a.val = j + 1 := by omega
        rw [hv, FinPerm.swap_apply_right]
        rfl
      · rw [FinPerm.swap_apply_of_ne_of_ne (by simp [Atom.ofNat]; omega)
            (by simp [Atom.ofNat]; omega),
          FinPerm.swap_apply_of_ne_of_ne (by simp [Atom.ofNat]; omega)
            (by simp [Atom.ofNat]; omega)]
        simp only [Atom.ofNat]
        omega

/-- Substitution of a fresh index is also a permutation; together with `lift_is_dpm` this is
what turns the `dLAM`-body of `dABS t = dLAM i t₀` into a permutation of `t₀`
(HOL `fresh_dpm_sub`, `dLAM_alt_dpm`).

Note that the freshness hypothesis is on the index `i` being substituted *in*, not on the index
`j` being substituted *for*: substituting `dV i` for `j` in a term in which `i` does not occur
free is exactly the transposition `[i ↔ j]`. -/
theorem dsub_var_eq_dpm {t : Term} {i j : ℕ} (h : i ∉ dFV t) :
    dsub (var i) j t = (FinPerm.swap (Atom.ofNat i) (Atom.ofNat j)) • t := by
  induction t generalizing i j with
  | var m =>
      simp only [mem_dFV_var] at h
      rw [dsub_var, dpm_var]
      by_cases hm : m = j
      · subst hm
        rw [ite_eq_left rfl, FinPerm.swap_apply_right]
        rfl
      · rw [ite_eq_right hm, FinPerm.swap_apply_of_ne_of_ne (by simp [Atom.ofNat]; omega)
          (by simp [Atom.ofNat]; omega)]
        rfl
  | app t u iht ihu =>
      simp only [mem_dFV_app, not_or] at h
      rw [dsub_app, dpm_app, iht h.1, ihu h.2]
  | abs t ih =>
      simp only [mem_dFV_abs] at h
      rw [dsub_abs, dpm_abs, incPerm_zero_swap, lift_var]
      simp only [Nat.not_lt_zero, ite_false]
      exact congrArg abs (ih h)

/-- Putting **Lemma 14** and `dsub_var_eq_dpm` together: `dLAM i t` is `dABS` applied to a
permutation of `t`, and the permutation only depends on `i` and on a bound `n` for the free
indices of `t` — not on `t` itself.  This uniformity is what makes **Theorem 15** work. -/
theorem dLAM_eq_abs_dpm (i n : ℕ) (t : Term) (h : ∀ k ∈ dFV t, k ≤ n) :
    dLAM i t =
      abs ((FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1)) * liftingPerm 0 n) • t) := by
  have h0 : (0 : ℕ) ∉ dFV (lift t 0) := by
    simp only [mem_dFV_lift]
    rintro (⟨hlt, _⟩ | ⟨hlt, _⟩) <;> omega
  rw [dLAM, dsub_var_eq_dpm h0, lift_eq_dpm t n h 0, mul_smul]

/-! ### `dLAM` is injective up to a swap -/

/-- Lifting is injective (HOL `lift_11`). -/
theorem lift_inj {t u : Term} {n : ℕ} (h : lift t n = lift u n) : t = u := by
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
theorem zero_not_mem_dFV_lift (t : Term) : (0 : ℕ) ∉ dFV (lift t 0) := by
  simp only [mem_dFV_lift]
  rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega

/-- The free indices of `lift t 0`, above `0`. -/
theorem mem_dFV_lift_succ (u : Term) (i : ℕ) : i + 1 ∈ dFV (lift u 0) ↔ i ∈ dFV u := by
  simp only [mem_dFV_lift, Nat.add_sub_cancel]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · omega
    · exact h
  · intro h; exact Or.inr ⟨by omega, h⟩

/-- Distinct indices give distinct atoms. -/
theorem ofNat_ne_ofNat {k l : ℕ} (h : k ≠ l) : Atom.ofNat k ≠ Atom.ofNat l :=
  fun hc => h (congrArg Atom.val hc)

/-- The permutation form of `dLAM`, obtained from `dsub_var_eq_dpm`: the substitution inside
`dLAM` is the transposition `[0 ↔ i+1]`. -/
theorem dLAM_eq_abs_swap (i : ℕ) (t : Term) :
    dLAM i t = abs ((FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1))) • lift t 0) := by
  rw [dLAM, dsub_var_eq_dpm (zero_not_mem_dFV_lift t)]

/-- The permutation action on de Bruijn terms is injective. -/
theorem dpm_left_cancel {π : FinPerm} {t u : Term} (h : π • t = π • u) : t = u := by
  have h' := congrArg (fun x : Term => π⁻¹ • x) h
  simpa only [inv_smul_smul] using h'

/-- The heart of `dLAM_eq_dLAM_iff`: two transposed lifts agree only if the two bodies are
related by the transposition `[i ↔ j]` and `i` is fresh for the second one. -/
theorem swap_lift_eq_aux {i j : ℕ} {t u : Term} (hij : i ≠ j)
    (h : (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1))) • lift t 0
        = (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (j + 1))) • lift u 0) :
    i ∉ dFV u ∧ t = (FinPerm.swap (Atom.ofNat i) (Atom.ofNat j)) • u := by
  have hA : lift t 0 = (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1))
      * FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (j + 1))) • lift u 0 := by
    rw [mul_smul, ← h, ← mul_smul, FinPerm.swap_swap, one_smul]
  have hτi : (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1))
      * FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (j + 1))) (Atom.ofNat (i + 1))
      = Atom.ofNat 0 := by
    rw [FinPerm.mul_apply,
      FinPerm.swap_apply_of_ne_of_ne (ofNat_ne_ofNat (by omega)) (ofNat_ne_ofNat (by omega)),
      FinPerm.swap_apply_right]
  have hiB : i + 1 ∉ dFV (lift u 0) := by
    intro hmem
    refine zero_not_mem_dFV_lift t ?_
    rw [hA, mem_dFV_dpm]
    exact ⟨i + 1, hmem, by rw [hτi]; rfl⟩
  refine ⟨fun hc => hiB ((mem_dFV_lift_succ u i).mpr hc), ?_⟩
  have hfix : ((FinPerm.swap (Atom.ofNat (i + 1)) (Atom.ofNat (j + 1)))⁻¹
      * (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1))
        * FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (j + 1)))) • lift u 0 = lift u 0 := by
    refine supports_dFV (lift u 0) _ (fun a ha => ?_)
    simp only [Finset.mem_image] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    have hk0 : k ≠ 0 := fun hc => zero_not_mem_dFV_lift u (hc ▸ hk)
    have hki : k ≠ i + 1 := fun hc => hiB (hc ▸ hk)
    rw [FinPerm.mul_apply, FinPerm.swap_inv]
    rcases eq_or_ne k (j + 1) with rfl | hkj
    · rw [FinPerm.mul_apply, FinPerm.swap_apply_right, FinPerm.swap_apply_left,
        FinPerm.swap_apply_left]
    · rw [FinPerm.mul_apply,
        FinPerm.swap_apply_of_ne_of_ne (ofNat_ne_ofNat hk0) (ofNat_ne_ofNat hkj),
        FinPerm.swap_apply_of_ne_of_ne (ofNat_ne_ofNat hk0) (ofNat_ne_ofNat hki),
        FinPerm.swap_apply_of_ne_of_ne (ofNat_ne_ofNat hki) (ofNat_ne_ofNat hkj)]
  have hAρ : lift t 0 = (FinPerm.swap (Atom.ofNat (i + 1)) (Atom.ofNat (j + 1))) • lift u 0 := by
    rw [hA, show (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1))
        * FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (j + 1)))
      = FinPerm.swap (Atom.ofNat (i + 1)) (Atom.ofNat (j + 1))
        * ((FinPerm.swap (Atom.ofNat (i + 1)) (Atom.ofNat (j + 1)))⁻¹
          * (FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (i + 1))
            * FinPerm.swap (Atom.ofNat 0) (Atom.ofNat (j + 1))))
      by rw [← mul_assoc, mul_inv_cancel, one_mul], mul_smul, hfix]
  rw [← incPerm_zero_swap, ← lift_dpm] at hAρ
  exact lift_inj hAρ

/-- `dLAM` is injective up to a transposition of the two abstracted indices (HOL `dLAM_11`,
the analogue of `LAM_eq_thm` for `Λα`).  This is the fact that makes `dB'` behave exactly like
the α-quotiented syntax. -/
theorem dLAM_eq_dLAM_iff {i j : ℕ} {t u : Term} :
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
      rw [dpm_dLAM, FinPerm.swap_apply_right] at hsupp
      exact hsupp

/-! ### Theorem 15 -/

/-- **Theorem 15** (Abstraction Congruences Correspond): if `R` is equivariant, then the
`dABS`-congruence rule and the `dLAM`-congruence rule for `R` are equivalent
(HOL `dABS_rules_are_dLAM_compatible`).  The generality of the statement is what makes it
reusable for η-reduction in Section 4.4. -/
theorem dABS_rules_are_dLAM_compatible (R : Term → Term → Prop)
    (hR : ∀ (π : FinPerm) (t u : Term), R (π • t) (π • u) ↔ R t u) :
    (∀ t u, R t u → R (abs t) (abs u)) ↔ (∀ i t u, R t u → R (dLAM i t) (dLAM i u)) := by
  constructor
  · intro habs i t u htu
    obtain ⟨n₁, hn₁⟩ := dFV_bounded t
    obtain ⟨n₂, hn₂⟩ := dFV_bounded u
    set n := max n₁ n₂ with hn
    have ht : ∀ k ∈ dFV t, k ≤ n := fun k hk => by have := hn₁ k hk; omega
    have hu : ∀ k ∈ dFV u, k ≤ n := fun k hk => by have := hn₂ k hk; omega
    rw [dLAM_eq_abs_dpm i n t ht, dLAM_eq_abs_dpm i n u hu]
    exact habs _ _ ((hR _ t u).mpr htu)
  · intro hlam t u htu
    obtain ⟨i, hi⟩ := dfresh_exists (app (abs t) (abs u))
    simp only [mem_dFV_app, not_or] at hi
    obtain ⟨t₀, ht₀⟩ := dABS_renamed hi.1
    obtain ⟨u₀, hu₀⟩ := dABS_renamed hi.2
    obtain ⟨n₁, hn₁⟩ := dFV_bounded t₀
    obtain ⟨n₂, hn₂⟩ := dFV_bounded u₀
    set n := max n₁ n₂ with hn
    have ht : ∀ k ∈ dFV t₀, k ≤ n := fun k hk => by have := hn₁ k hk; omega
    have hu : ∀ k ∈ dFV u₀, k ≤ n := fun k hk => by have := hn₂ k hk; omega
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
