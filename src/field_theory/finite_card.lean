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

lemma degree_Xq_X {β : Type v} [discrete_field β] {q : ℕ} (hq : q > 1) :
  degree (X^q - X : polynomial β) = q :=
have (X^q - X : polynomial β) = X^q + -X, from rfl,
begin
  rw [this, ←degree_X_pow q, add_comm],
  apply degree_add_eq_of_degree_lt,
  rw[degree_neg, degree_X, degree_X_pow],
  exact with_bot.coe_lt_coe.mpr hq
end

/-- The set of roots of x^p^n-x in β where char(β) = p forms a subfield of β.
 This is because it is the invariant subfield of the n-th iterate of the p-frobenius -/
theorem subfield_Xq_X (β : Type v) [discrete_field β] (p : ℕ) [char_p β p] (hp : nat.prime p) (n : ℕ) (hn : n > 0) :
  is_subfield (↑(X^(p^n) - X : polynomial β).roots : set β) :=
let f := (X^(p^n) - X : polynomial β) in
suffices (↑(X^(p^n) - X : polynomial β).roots : set β) = {x | (frobenius β (p^n)) x = x},
  by rw [this, ←nat.succ_pred_eq_of_pos hn];
  exact is_field_hom.invariant_subfield (frobenius β (p^((n-1)+1))),
have hq : 1 < p^n, from nat.pow_lt_pow_of_lt_right (hp.gt_one) hn,
have h0 : (X^p^n - X : polynomial β) ≠ 0, from
  ne_zero_of_degree_gt (by rw[degree_Xq_X hq, with_bot.coe_lt_coe]; exact hq),
set.ext $ λ x,
calc x ∈ (↑(X^p^n - X : polynomial β).roots : set β)
      ↔ is_root (X^p^n - X) x : by rw [finset.mem_coe, mem_roots h0]
  ... ↔ -x + x^p^n = 0        : by simp --only [polynomial.eval_X,polynomial.eval_neg,iff_self,add_comm,polynomial.eval_pow,polynomial.eval_add,sub_eq_add_neg,polynomial.is_root.def]
  ... ↔ x^p^n = x             : by rw[←add_left_inj x, add_zero, add_neg_cancel_left]




end finite_field
