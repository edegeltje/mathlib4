/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Definition of Cayley graphs

This file defines and proves several fact about Cayley graphs.
A Cayley graph over type `G` with jumps `s : Set G` is a graph in which two vertices `u ≠ v`
are adjacent if and only if there is some `g ∈ s` such that `u * g = v` or `v * g = u`.
The elements of `s` are called jumps.

## Main declarations

* `SimpleGraph.mulCayley s`: the Cayley graph over `G` induced by [Mul G] with jumps `s`.
* `SimpleGraph.addCayley s`: the Cayley graph over `G` induced by [Add G] with jumps `s`.
-/

@[expose] public section

namespace SimpleGraph

/-- the Cayley graph induced by an operation `Mul G` with jumps `s` -/
@[to_additive /-- the Cayley graph induced by an operation `Add G` with jumps `s` -/]
def mulCayley {G : Type*} (s : Set G) [Mul G] : SimpleGraph G :=
  fromRel (∃ g ∈ s, · * g = ·)

variable {G : Type*} (s : Set G)

@[to_additive]
lemma mulCayley_adj' [Mul G] (u v : G) :
    (mulCayley s).Adj u v ↔ u ≠ v ∧ ∃ g ∈ s, u * g = v ∨ u = v * g := by
  simp [mulCayley,← exists_or,← and_or_left, eq_comm]

@[to_additive]
lemma mulCayley_adj [Group G] (u v : G) :
    (mulCayley s).Adj u v ↔ u ≠ v ∧ (u⁻¹ * v ∈ s ∨ v⁻¹ * u ∈ s) := by
  simp [mulCayley_adj',← eq_inv_mul_iff_mul_eq (b := u),← inv_mul_eq_iff_eq_mul (a := v),
    and_or_left, exists_or]

@[to_additive]
theorem mulCayley_eq_erase_one [MulOneClass G] : mulCayley s = mulCayley (s \ {1}) := by
  ext u v
  simp only [mulCayley_adj', Set.mem_diff, Set.mem_singleton_iff, and_congr_right_iff, and_assoc]
  intro h
  congr! 3
  rw [iff_and_self]
  rintro _ rfl
  simp_all

@[to_additive]
theorem mulCayley_eq_union_one [MulOneClass G] : mulCayley s = mulCayley (s ∪ {1}) := by
  rw [mulCayley_eq_erase_one s, mulCayley_eq_erase_one (s ∪ _)]
  simp

@[to_additive]
theorem mulCayley_eq_symm [Group G] : mulCayley s = mulCayley (s ∪ (s⁻¹)) := by
  ext u v
  simp [mulCayley_adj, or_comm]

@[to_additive]
instance [Group G] [DecidableEq G] [DecidablePred (· ∈ s)] : DecidableRel (mulCayley s).Adj :=
  fun u v => decidable_of_iff (u ≠ v ∧ (u⁻¹ * v ∈ s ∨ v⁻¹ * u ∈ s)) (mulCayley_adj s u v).symm

@[to_additive]
instance [Mul G] [Fintype G] [DecidableEq G] [DecidablePred (· ∈ s)] :
    DecidableRel (mulCayley s).Adj := fun u v =>
  decidable_of_iff (u ≠ v ∧ ∃ g ∈ s, u * g = v ∨ u = v * g) (mulCayley_adj' s u v).symm

@[to_additive]
theorem mulCayley_adj_mul_left_iff [Semigroup G] [IsLeftCancelMul G] {s : Set G} {u v d : G} :
    (mulCayley s).Adj u v ↔ (mulCayley s).Adj (d * u) (d * v) := by
  simp [mulCayley_adj', mul_assoc]

@[to_additive (attr := gcongr)]
theorem mulCayley_mono [Mul G] ⦃U V : Set G⦄ (hUV : U ⊆ V) : mulCayley U ≤ mulCayley V := by
  intro _ _
  simp_rw [mulCayley_adj']
  gcongr

@[to_additive (attr := simp)]
theorem mulCayley_empty [Mul G] : mulCayley (∅ : Set G) = ⊥ := by
  ext _ _
  simp [mulCayley_adj']

@[to_additive (attr := simp)]
theorem mulCayley_singleton_one [MulOneClass G] : mulCayley ({1} : Set G) = ⊥ := by
  rw [mulCayley_eq_erase_one, Set.diff_self, mulCayley_empty]

@[to_additive (attr := simp)]
theorem mulCayley_univ [Group G] : mulCayley (Set.univ : Set G) = ⊤ := by
  ext _ _
  simp [mulCayley_adj]

@[to_additive (attr := simp)]
theorem mulCayley_compl_singleton_one [Group G] : mulCayley ({1}ᶜ : Set G) = ⊤ := by
  rw [Set.compl_eq_univ_diff,← mulCayley_eq_erase_one, mulCayley_univ]

end SimpleGraph
