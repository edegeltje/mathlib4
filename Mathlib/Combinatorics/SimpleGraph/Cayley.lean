/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Definition of circulant graphs

This file defines and proves several fact about Cayley graphs.
A Cayley graph over type `G` with jumps `s : Set G` is a graph in which two vertices `u` and `v`
are adjacent if and only if there is some `g ∈ G` such that `u * g = v` or `v * g = u`.
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

@[to_additive (attr := simp)]
lemma mulCayley_adj' [Mul G] (u v : G) :
  (mulCayley s).Adj u v ↔ u ≠ v ∧ ∃ g ∈ s, (u * g = v ∨ u = v * g) := by
  simp only [mulCayley, fromRel_adj, ne_eq, and_congr_right_iff]
  intro h
  simp_rw [← exists_or,← and_or_left]
  apply exists_congr
  simp only [and_congr_right_iff]
  exact fun _ _ => or_congr Iff.rfl eq_comm

-- it's important this lemma gets higher priority than `mulCayley_adj'`, because when
-- multiplication has an inverse, we can give a simpler characterization of the relation
@[to_additive (attr := simp high)]
lemma mulCayley_adj [Group G] (u v : G) :
  (mulCayley s).Adj u v ↔ u ≠ v ∧ (u⁻¹ * v ∈ s ∨ v⁻¹ * u ∈ s) := by
  simp only [mulCayley_adj', ne_eq, and_congr_right_iff]
  intro
  simp_rw [← eq_inv_mul_iff_mul_eq (b := u),← inv_mul_eq_iff_eq_mul (a := v), and_or_left,
    exists_or]
  simp -- ↓existsAndEq simproc for the win

@[to_additive]
theorem mulCayley_eq_erase_one [MulOneClass G] : mulCayley s = mulCayley (s \ {1}) := by
  ext u v
  simp only [mulCayley_adj', Set.mem_diff, Set.mem_singleton_iff, and_congr_right_iff]
  intro h
  apply exists_congr
  simp only [and_congr_left_iff, iff_self_and]
  rintro g hg₁ hg₂ rfl
  apply h
  simpa using hg₁

@[to_additive]
theorem mulCayley_eq_union_one [MulOneClass G] : mulCayley s = mulCayley (s ∪ {1}) := by
  rw [mulCayley_eq_erase_one s,mulCayley_eq_erase_one (s ∪ _)]
  simp

@[to_additive]
theorem mulCayley_eq_symm [Group G] : mulCayley s = mulCayley (s ∪ (s⁻¹)) := by
  ext u v
  simp only [mulCayley_adj, ne_eq, Set.involutiveInv, Set.mem_union, Set.mem_inv, mul_inv_rev,
    inv_inv, and_congr_right_iff, iff_self_or]
  exact fun _ => Or.symm

@[to_additive]
instance [Group G] [DecidableEq G] [DecidablePred (· ∈ s)] : DecidableRel (mulCayley s).Adj :=
  fun u v => decidable_of_iff (u ≠ v ∧ (u⁻¹ * v ∈ s ∨ v⁻¹ * u ∈ s)) (mulCayley_adj s u v).symm

@[to_additive]
theorem mulCayley_adj_mul_left_iff [Semigroup G] [IsLeftCancelMul G] {s : Set G} {u v d : G} :
    (mulCayley s).Adj u v ↔ (mulCayley s).Adj (d * u) (d * v) := by
  simp only [mulCayley_adj', ne_eq, mul_right_inj, mul_assoc]

@[to_additive (attr := gcongr)]
theorem mulCayley_mono [Mul G] ⦃U V : Set G⦄ (hUV : U ⊆ V) : mulCayley U ≤ mulCayley V := by
  intro _ _
  simp_rw [mulCayley_adj']
  gcongr

@[to_additive (attr := simp)]
theorem mulCayley_bot [Mul G] : mulCayley (∅ : Set G) = ⊥ := by
  ext _ _
  simp

@[to_additive (attr := simp)]
theorem mulCayley_top_eq_of_group [Group G] : mulCayley (Set.univ : Set G) = ⊤ := by
  ext _ _
  simp

end SimpleGraph
