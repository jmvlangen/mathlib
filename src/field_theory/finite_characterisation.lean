/-
Copyright (c) 2019 Casper Putz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joey van Langen, Casper Putz
-/

import algebra.char_p data.zmod.basic linear_algebra.basis data.polynomial
import field_theory.splitting_field field_theory.subfield

universes u

namespace finite_field

/- Results about the cardinality of finitie fields -/
section card

variables (α : Type u) [discrete_field α] [fintype α]

theorem card (p : ℕ) [char_p α p] : ∃ (n : ℕ+), nat.prime p ∧ fintype.card α = p^(n : ℕ) :=
have hp : nat.prime p, from char_p.char_is_prime α p,
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

end card

end finite_field

/- Some results about the polynomial X^q - X.
    In particular some results when q = p^n for p prime
    and α of characteristic p -/
namespace Xq_sub_X

open polynomial

variables {α : Type u} [discrete_field α]

lemma degree {q : ℕ} (hq : q > 1) : degree (X^q - X : polynomial α) = q :=
have (X^q - X : polynomial α) = X^q + -X, from rfl,
begin
  rw [this, ←degree_X_pow q, add_comm],
  apply degree_add_eq_of_degree_lt,
  rw[degree_neg, degree_X, degree_X_pow],
  exact with_bot.coe_lt_coe.mpr hq
end

lemma leading_coeff {q : ℕ} (hq : q > 1) :
  leading_coeff (X^q - X : polynomial α) = 1 :=
by { rw[sub_eq_add_neg, add_comm, leading_coeff_add_of_degree_lt, leading_coeff_pow, leading_coeff_X, one_pow],
  rwa[degree_X_pow, degree_neg, degree_X, ←with_bot.coe_one, with_bot.coe_lt_coe] }

lemma ne_zero {q : ℕ} (hq : q > 1) : (X^q - X : polynomial α) ≠ 0 :=
ne_zero_of_degree_gt (by rwa[degree hq, with_bot.coe_lt_coe])

theorem roots_is_subfield {p : ℕ} [char_p α p] (hp : nat.prime p) {n : ℕ} (hn : n > 0) :
  is_subfield (↑(X^p^n - X : polynomial α).roots : set α) :=
let f := (X^p^n - X : polynomial α) in
suffices (↑f.roots : set α) = {x | (frobenius α (p^n)) x = x},
  by rw [this, ←nat.succ_pred_eq_of_pos hn];
  sorry, -- exact is_field_hom.fixed_subfield (frobenius α (p^((n-1)+1))), --Does not work for some reason?
have hq : 1 < p^n, from nat.pow_lt_pow_of_lt_right (hp.gt_one) hn,
set.ext $ λ x,
calc x ∈ (↑f.roots : set α)
      ↔ is_root f x    : by rw [finset.mem_coe, mem_roots (ne_zero hq)]
  ... ↔ -x + x^p^n = 0 : by simp --only [polynomial.eval_X,polynomial.eval_neg,iff_self,add_comm,polynomial.eval_pow,polynomial.eval_add,sub_eq_add_neg,polynomial.is_root.def]
  ... ↔ x^p^n = x      : by rw[←add_left_inj x, add_zero, add_neg_cancel_left]

lemma derivative {p : ℕ} [char_p α p] (hp : nat.prime p) {n : ℕ} (hn : n > 0) :
  derivative (X^p^n - X : polynomial α) = C (-1) :=
show derivative (X^p^n + -X : polynomial α) = C (-1),
begin
  rw[neg_eq_neg_one_mul, ←one_mul (X^p^n), ←C_1, ←C_neg, derivative_add, derivative_monomial],
  rw[(char_p.cast_eq_zero_iff α p (p^n)).mpr],
  { rw[mul_zero, C_0, zero_mul, zero_add, ←pow_one X, derivative_monomial, nat.sub_self,
      pow_zero, nat.cast_one, mul_one, mul_one] },
  exact suffices p^1 ∣ p^n, by rwa[nat.pow_one] at this,
    nat.pow_dvd_pow p (nat.one_le_of_lt hn)
end

lemma distinct_roots {p : ℕ} [char_p α p] (hp : nat.prime p) {n : ℕ} (hn : n > 0) (a : α) :
  is_root (X^(p^n) - X) a → root_multiplicity a (X^p^n - X) = 1 :=
sorry
-- have hq : 1 < p^n, from nat.pow_lt_pow_of_lt_right (hp.gt_one) hn,
-- eq.symm $ nat.eq_of_lt_succ_of_not_lt
--   (nat.succ_lt_succ $ (root_multiplicity_pos_iff_is_root $ Xq_X_ne_zero hq).mpr $
--     by rwa[finset.mem_coe, mem_roots (Xq_X_ne_zero hq)] at hx)
--   (λ _ : 1 < root_multiplicity x (X ^ p ^ n - X),
--   have is_root (C (-1)) x,
--     begin
--       rw[←dvd_iff_is_root,←derivative_Xq_X p hp n hn,←pow_one (X - C x),←nat.succ_sub_one 1],
--       refine derivative_dvd (nat.succ_pos 1) _ (monic_X_sub_C x) _,
--         { refine dvd_trans (pow_dvd_pow (X-C x) _) (pow_root_multiplicity_dvd _ _), rwa[nat.succ_le_iff] },
--         { apply_instance }
--     end,
--   absurd (show (1 : β) = 0, by simpa) one_ne_zero)

end Xq_sub_X
