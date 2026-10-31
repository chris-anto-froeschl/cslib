/-
Copyright (c) 2024 Bas Spitters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import Cslib.Logics.Nominal.Atom
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Finite Permutations

This file defines finite permutations of atoms - permutations that only move
finitely many atoms.

## Main definitions

* `FinPerm` - Finite permutations (bijections on atoms with finite support)
* `FinPerm.swap` - Transposition of two atoms

## Implementation notes

Since `Atom` is infinite (not `Fintype`), we cannot use Mathlib's `Perm.support`
directly (which requires `Fintype`). Instead, we define a predicate
`IsFinitelySupported` that states a permutation has finite support, and define
`FinPerm` as the subtype of permutations satisfying this predicate.

This file is ported from the `spitters/nominal-lean` repository.

## References

* Pitts, *Nominal Sets: Names and Symmetry in Computer Science*,
  Cambridge University Press, 2013, Chapter 2.
* Larsen and Schürmann, *Nominal State-Separating Proofs*, IACR ePrint 2025/598, the SSProve
  `Nominal/` layer this development ports.
* SSProve `theories/Crypt/nominal/Nominal.v`
-/

@[expose] public section

namespace Cslib.Logic.Nominal

open Equiv

/-- A permutation is finitely supported if there exists a finite set outside
    of which it acts as the identity. -/
def IsFinitelySupported (π : Perm Atom) : Prop :=
  ∃ s : Finset Atom, ∀ a, a ∉ s → π a = a

/-- The type of finitely-supported permutations of atoms. -/
def FinPerm := { π : Perm Atom // IsFinitelySupported π }

namespace FinPerm

/-- Coercion to underlying permutation -/
instance : CoeOut FinPerm (Perm Atom) := ⟨Subtype.val⟩

/-- Apply permutation to an atom -/
def apply (π : FinPerm) (a : Atom) : Atom := π.val a

instance : CoeFun FinPerm (fun _ => Atom → Atom) := ⟨apply⟩

theorem apply_def (π : FinPerm) (a : Atom) : π a = π.val a := rfl

theorem val_injective : Function.Injective (Subtype.val : FinPerm → Perm Atom) :=
  Subtype.val_injective

@[ext]
theorem ext {π₁ π₂ : FinPerm} (h : ∀ a, π₁ a = π₂ a) : π₁ = π₂ :=
  val_injective (Perm.ext h)

/-- A witness of finite support for a permutation -/
noncomputable def suppWitness (π : FinPerm) : Finset Atom :=
  Classical.choose π.prop

theorem suppWitness_spec (π : FinPerm) : ∀ a, a ∉ π.suppWitness → π a = a :=
  Classical.choose_spec π.prop

/-- Identity permutation -/
def one : FinPerm :=
  ⟨1, ∅, by simp⟩

instance : One FinPerm := ⟨one⟩

theorem one_apply (a : Atom) : (1 : FinPerm) a = a := rfl

/-- Composition of finite permutations -/
def mul (π₁ π₂ : FinPerm) : FinPerm :=
  ⟨π₁.val * π₂.val,
   π₁.suppWitness ∪ π₂.suppWitness, by
     intro a ha
     simp only [Finset.mem_union, not_or] at ha
     simp only [Perm.coe_mul, Function.comp_apply]
     have h2 := π₂.suppWitness_spec a ha.2
     have h1 := π₁.suppWitness_spec a ha.1
     simp only [apply_def] at h2 h1
     rw [h2, h1]⟩

instance : Mul FinPerm := ⟨mul⟩

theorem mul_apply (π₁ π₂ : FinPerm) (a : Atom) : (π₁ * π₂) a = π₁ (π₂ a) := rfl

/-- Inverse of a finite permutation -/
def inv (π : FinPerm) : FinPerm :=
  ⟨π.val⁻¹, π.suppWitness, by
     intro a ha
     have h := π.suppWitness_spec a ha
     simp only [apply_def] at h
     simp only [Perm.inv_eq_iff_eq]
     exact h.symm⟩

instance : Inv FinPerm := ⟨inv⟩

/-- Finite permutations form a group -/
instance : Group FinPerm where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel π := FinPerm.ext fun a => π.val.symm_apply_apply a

/-- Transposition: swap two atoms -/
noncomputable def swap (a b : Atom) : FinPerm :=
  ⟨Equiv.swap a b, if a = b then ∅ else {a, b}, by
     intro c hc
     by_cases hab : a = b
     · simp [hab, Equiv.swap_self]
     · simp only [hab, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
       exact Equiv.swap_apply_of_ne_of_ne hc.1 hc.2⟩

theorem swap_apply_left (a b : Atom) : swap a b a = b := Equiv.swap_apply_left a b

theorem swap_apply_right (a b : Atom) : swap a b b = a := Equiv.swap_apply_right a b

theorem swap_apply_of_ne_of_ne {a b c : Atom} (hca : c ≠ a) (hcb : c ≠ b) :
    swap a b c = c := Equiv.swap_apply_of_ne_of_ne hca hcb

theorem swap_val (a b : Atom) : (swap a b).val = Equiv.swap a b := rfl

theorem swap_self (a : Atom) : swap a a = 1 :=
  FinPerm.ext fun c => by rw [apply_def, swap_val, Equiv.swap_self]; rfl

theorem swap_comm (a b : Atom) : swap a b = swap b a :=
  FinPerm.ext fun c => congrArg (· c) (Equiv.swap_comm a b)

theorem swap_swap (a b : Atom) : swap a b * swap a b = 1 :=
  FinPerm.ext fun c => Equiv.swap_apply_self a b c

theorem swap_inv (a b : Atom) : (swap a b)⁻¹ = swap a b :=
  inv_eq_of_mul_eq_one_right (swap_swap a b)

end FinPerm

end Cslib.Logic.Nominal
