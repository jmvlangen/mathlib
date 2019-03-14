/-
Copyright (c) 2019 Casper Putz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joey van Langen, Casper Putz
-/

import algebra.char_p data.zmod.basic linear_algebra.basis data.polynomial
import field_theory.splitting_field field_theory.subfield

universes u v
variables {α : Type u} [discrete_field α] [fintype α]

namespace finite_field

theorem card (p : ℕ) [char_p α p] : ∃ (n : ℕ+), nat.prime p ∧ fintype.card α = p^(n : ℕ) :=
have hp : nat.prime p, from char_p.is_prime α p,
have V : vector_space (zmodp p hp) α, from {..zmod.to_module'},
let ⟨n, h⟩ := @vector_space.card_fintype' _ _ _ _ V _ _ in
have hn : n > 0, from or.resolve_left (nat.eq_zero_or_pos n)
  (assume h0 : n = 0,
  have fintype.card α = 1, by rw[←nat.pow_zero (fintype.card _), ←h0]; exact h,
  have (1 : α) = 0, from (fintype.card_le_one_iff.mp (le_of_eq this)) 1 0,
  absurd this one_ne_zero),
⟨⟨n, hn⟩, hp, fintype.card_fin p ▸ h⟩

theorem card' : ∃ (p : ℕ) (n : ℕ+), nat.prime p ∧ fintype.card α = p^(n : ℕ) :=
let ⟨p, hc⟩ := char_p.exists α in ⟨p, @finite_field.card α _ _ p hc⟩


open polynomial

--note: the characteristic of β follows from i : α → β
theorem poly_subfield (p : ℕ) [char_p α p] (n : ℕ) (β : Type v) [discrete_field β] [char_p β p]
  (i : α → β) [is_field_hom i] (h : splits i (X^(p^n) - X)) :
  is_subfield (↑(X^(p^n) - X : polynomial β).roots : set β) :=
  let f := (X^(p^n) - X : polynomial β) in
  have h0 : f ≠ 0, from sorry,
  have hp : nat.prime p, from char_p.is_prime α p,
  { zero_mem := begin rw [finset.mem_coe, mem_roots], simp,
      exact zero_pow (nat.pow_pos hp.pos n), exact h0 end,
    one_mem := by rw [finset.mem_coe, mem_roots]; simp; exact h0,
    add_mem := λ a b ha hb, begin rw [finset.mem_coe, mem_roots] at ha hb ⊢, simp at ha hb ⊢,
      rw [add_pow_n_char β hp a b],
      exact calc -a + (-b + (a^p^n + b^p^n))
          = (-a + a^p^n) + (-b + b^p^n) : by simp only [neg_inj', add_comm, eq_self_iff_true, add_right_inj, add_left_comm]
      ... = 0                           : by simp only [ha, hb, add_zero, eq_self_iff_true],
      repeat {exact h0} end,
    neg_mem := λ a ha, begin rw [finset.mem_coe, mem_roots] at ha ⊢, simp at ha ⊢,
      exact calc a + -a ^ p ^ n = -(-a - -a^p^n) : by simp only [add_comm, eq_self_iff_true, neg_add_rev, add_right_inj, neg_neg, sub_eq_add_neg]
                            ... = -(-a +  a^p^n) : sorry
                            ... = 0              : by simp only [ha, eq_self_iff_true, neg_zero],
      repeat {exact h0} end,
    mul_mem := λ a b ha hb, begin rw [finset.mem_coe, mem_roots] at ha hb ⊢, simp at ha hb ⊢,
      have ha' : a^p^n = a := by rw[←add_left_inj (-a)]; simp only [ha, eq_self_iff_true, add_left_neg],
      have hb' : b^p^n = b := by rw[←add_left_inj (-b)]; simp only [hb, eq_self_iff_true, add_left_neg],
      rw[←add_left_inj (a*b), mul_pow],
      simp only [ha', hb', add_zero, eq_self_iff_true, add_left_neg],
      repeat {exact h0}
    end,
    inv_mem := λ a ha0 ha, begin rw [finset.mem_coe, mem_roots] at ha ⊢, simp at ha ⊢,
      have ha' : a^p^n = a := by rw[←add_left_inj (-a)]; simp only [ha, eq_self_iff_true, add_left_neg],
      exact calc -a⁻¹ + a⁻¹^p^n = -(a^p^n)⁻¹ + a⁻¹^p^n  : by rw[ha']
                            ... = -(a⁻¹^p^n) + a⁻¹^p^n  : sorry
                            ... = 0                     : by simp only [eq_self_iff_true, add_left_neg],
      repeat {exact h0}
    end }

end finite_field
