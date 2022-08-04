import Theorem3

variables {d : ℕ} (hd: nonsquare (d:ℤ))
include hd 

lemma d_gt_one : 1 < real.sqrt d:=
begin
  rw ← real.sqrt_one, rw real.sqrt_lt_sqrt_iff, 
  {norm_cast,
  by_contra',
  interval_cases d, 
    { have h1:= hd 0,
      norm_cast at h1, },
    { have h1:= hd 1,
      norm_cast at h1,
      }},

    { linarith}
end

lemma pos_re_pos_im_gt_one {z : ℤ√d} (h1: 0 < z.re) (h2: 0 < z.im): 1 < zsqrt_eval z:=
begin
  have h3: (1: ℝ) ≤ z.re ∧ (1:ℝ) ≤ z.im,
    { norm_cast, split,  all_goals {linarith}, },  
  rw zsqrt_eval_def, rw ← zero_add (1:ℝ), apply add_lt_add (show (0:ℝ)< z.re, by linarith), 
  rw ← one_mul (1:ℝ), apply mul_lt_mul' h3.2 (@d_gt_one d hd) (show 0 ≤ (1:ℝ), by simp), linarith,
end

lemma zsqrt_recip_conj {z : ℤ√d} (h0: z.norm =1) (h1:0< zsqrt_eval z): 1/zsqrt_eval z = zsqrt_eval_conj z :=
begin
  apply_fun (λ (a:ℤ), (a:ℝ)) at h0, rw int.cast_one at h0, 
  rw ← h0,  rw ← eval_eval_conj_norm, field_simp [div_self, (show zsqrt_eval z ≠ 0, by linarith)], linarith, 
end


lemma pos_re_neg_im_lt_one {z : ℤ√d} (h0: z.norm =1 )(h1: 0 < z.re) (h2: 0 < z.im): 0 < zsqrt_eval_conj z ∧ zsqrt_eval_conj z < 1:=
begin
have h:= lt_trans (show 0<(1:ℝ), by linarith) (pos_re_pos_im_gt_one hd h1 h2),
rw ← zsqrt_recip_conj hd h0 h, split, 
{exact div_pos (show 0 < (1:ℝ), by linarith) h },
{rw ← one_div_lt (show 0 < (1:ℝ), by linarith), 
 { rw ← (show 1 = (1/1:ℝ), by ring), exact pos_re_pos_im_gt_one hd h1 h2, },
 exact h,
   }
end

lemma z_minus_recip {z:ℤ√d} (h: z.norm=1) (h1: 0< z.re) (h2: 0 < z.im): zsqrt_eval z-1/zsqrt_eval z = 2 * real.sqrt d *z.im:=
begin
  have h3:= lt_trans (show 0<(1:ℝ), by linarith) (pos_re_pos_im_gt_one hd h1 h2),
  rw [zsqrt_recip_conj hd h h3, zsqrt_eval_conj_def, zsqrt_eval_def], 
  simp, ring,
end

lemma im_lt_im_imp_sol_lt_sol {z1 z2 : ℤ√d} (h0: z1.norm =1 ) (g0: z2.norm =1) (h1: 0 < z1.re) (g1: 0 < z2.re) (h2: 0 < z1.im) (g2: 0 < z2.im) (h3: zsqrt_eval z1 < zsqrt_eval z2): z1.im < z2.im:=
begin
  --rw ← @int.cast_lt ℝ, 
  suffices: (z1.im :ℝ ) < z2.im,
    {assumption_mod_cast, },
  have i1: 2*real.sqrt d * z1.im < 2* real.sqrt d *z2.im,
    { rw ← z_minus_recip hd h0 h1 h2, rw ← z_minus_recip hd g0 g1 g2,
      apply sub_lt_sub h3 (one_div_lt_one_div_of_lt (lt_trans (show 0<(1:ℝ), by linarith) (pos_re_pos_im_gt_one hd h1 h2)) h3 ), },
  rw mul_lt_mul_left at i1,
    { assumption },
    { simp [lt_trans (show 0<(1:ℝ), by linarith) (d_gt_one hd)],}
end



theorem fundamental_pell_sol' (x:ℤ) : ∃ (y : ℕ), (y:ℤ)=|x|   :=
begin
use |x|.to_nat, simp only [int.to_nat_of_nonneg, abs_nonneg],
end

theorem exist_pell_solution_nat {d:ℕ} (hd: nonsquare d): ∃ (y :ℕ), ∃ (x:ℕ), (⟨x, y⟩ : ℤ√d).norm=1  ∧ 1 ≤ y:=
begin
  rcases exist_pell_solution hd with ⟨x, y, h1, h2⟩,
  cases lift_to_nat y (show 0 ≤ y, by linarith) with Y hY,
  cases lift_to_nat (|x|) (abs_nonneg x) with X hX,
  use [Y, X],  rw ← h1, rw ← pell_to_norm, norm_cast, simp * at *, linarith,
end



noncomputable def min_pell_y := @nat.find _ (classical.dec_pred (λ (n : ℕ), ∃ (x : ℕ), (⟨x, n⟩ : ℤ√d).norm=1 ∧ 1 ≤ n)) (exist_pell_solution_nat hd) 





example (a b c:ℤ  ) (h: a^2 =b^2)  : a=b ∨ a = -b:= 
begin
exact eq_or_eq_neg_of_sq_eq_sq a b h,
end

example (y:ℤ) (h: 0 ≤ y): ∃ (x:ℕ), (x:ℤ)=(y:ℤ):= 
begin
exact lift_to_nat y h,
end
-- ←h▸r (rw h at r)

-- 