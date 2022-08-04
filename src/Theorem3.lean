import Corollary2
import data.zmod.basic


/-
# Theorem 3: Existence of Pell solutions
The main goal of this final file is to prove that the equation x^2-dy^2=1 always has a nontrivial integer solution if d is a nonsquare natural number.
-/

variables {d : ℕ} {hd: nonsquare d}

lemma abs_eq_self1 (a:ℝ) (h: 0≤ a): abs a =a :=
begin
  exact abs_eq_self.mpr h,
end

/--Every pair in S has norm bounded by 2√d+1 and -(2√d+1). But S is infinite so there are infinitely many pairs with bounded norm.--/
lemma inf_bounded_pairs (a: (S d)) (hd: nonsquare (d:ℤ)): abs(((⟨a.val.1, a.val.2⟩ : ℤ√d).norm):ℝ)≤ (2:ℝ) *(real.sqrt d)+1:=
begin
  rcases a with ⟨a, a1, a2⟩,
  rw ← eval_eval_conj_norm,
  rw abs_mul, dsimp, 
  have h1: abs ((a.fst:ℝ) + (a.snd:ℝ) * (real.sqrt d))≤ 1/(a.snd:ℝ) +2*(real.sqrt d)* (a.snd),
  { have i1: ↑(a.fst) + ↑(a.snd) * real.sqrt ↑d = ↑(a.fst) - ↑(a.snd) * real.sqrt ↑d + 2*↑(a.snd) * real.sqrt ↑d:=by ring,
    rw i1,
    apply le_trans (abs_add _ _), apply add_le_add (le_of_lt a2), apply le_of_eq, repeat {rw abs_mul}, 
    rw abs_eq_self1 _ (show 0 ≤ (2:ℝ), by linarith), 
    rw abs_eq_self1 _ (show 0 ≤ (a.snd:ℝ), begin norm_cast, linarith end),
    rw abs_eq_self1 _ (real.sqrt_nonneg d),
    ring, },
    apply le_trans (mul_le_mul h1 (le_of_lt a2) (abs_nonneg _) (le_trans (abs_nonneg _) h1)),
    rw add_mul, simp [show (a.snd:ℝ ) ≠ 0, begin norm_cast, linarith end],rw add_comm, 
    apply add_le_add (show 2 * real.sqrt ↑d ≤ 2 * real.sqrt ↑d, by simp), 
    have h2: (0:ℝ) ≤  (↑(a.snd))⁻¹,
      { simp, linarith, },
    have h3: (↑(a.snd))⁻¹ ≤  (1:ℝ),
      { apply inv_le_one, norm_cast, linarith, },
    rw ← mul_one (1:ℝ),
    apply mul_le_mul h3 h3 h2 (show (0:ℝ) ≤ 1, by simp),
end

/--Define A the set of integers between 2√d+1 and -(2√d+1)--/
def A (d:ℕ):= {x: ℤ | abs(x:ℝ) ≤ 2*(real.sqrt d)+1}

/--A is finite. Needed for infinite Pigeonhole (which we formalize below): S infinite, A finite → infinitely many pairs with fixed norm.--/
lemma A_finite (d:ℕ) : set.finite (A d):=
begin
  refine bdd_below.finite_of_bdd_above _ _,
  { use ⌊-(2*(real.sqrt d)+1) ⌋,
    intros x hx,
    have h1:= int.floor_le (-(2*(real.sqrt d)+1)),
    have h2: -(2*(real.sqrt d)+1) ≤ x,
      { exact neg_le_of_abs_le hx, },
    have h3:= le_trans h1 h2,
    simp * at *, },

  { use ⌈(2*(real.sqrt d)+1)⌉,
    intros x hx,
    have h1:= int.le_ceil ((2*(real.sqrt d)+1)),
    have h2:  (x:ℝ) ≤ (2:ℝ)*(real.sqrt d)+(1:ℝ),
      { exact le_of_abs_le hx, },
    have h3:= ge_trans h1 h2,
    norm_cast at h3, exact h3,
  }
end

/--Norm can never be 0 if the 2nd coordinate is ≥ 1.--/
lemma pell_ne_zero (x y:ℤ) (hd: nonsquare d) (H: 1 ≤ y): x^2 -d*y^2 ≠ 0:=
begin
  by_contra,
  have h0:= nat.zero_le d, 
  have h1: y≠ 0,
    { linarith, },
  have h2: (d:ℝ) = (x/y)^2,
    { rw sub_eq_zero at h, field_simp * at *, norm_cast, rw h, },
  have h3: real.sqrt d = abs(x/y),
    { rw ← sq_abs at h2, rw real.sqrt_eq_iff_sq_eq (show 0 ≤ (d:ℝ), begin norm_cast, assumption end) (abs_nonneg _), rw h2, },
  have h4:= sqrtd_irrational hd, 
  rw abs_div at h3, 
  rw irrational_iff_ne_rational at h4,
  have h5:= h4 (abs x) (abs y),
  push_cast at h5,
  rw h3 at h5,
  exact h1 (false.rec (y = 0) (h5 rfl)),
end

lemma remainder_to_modeq (a b c:ℤ ): a%b=c%b ↔   a≡ c [ZMOD b]:= by refl
lemma sq_mul_sq (a b:ℤ ) :  a^2*b^2 = (a*b)^2 := by ring
lemma sub_sub_eq_sub_add (a b c:ℤ )  :a-(b-c) = a-b+c := by ring
lemma zero_or_one (a:ℤ) (h: 0 ≤ a) (h1: a<1): a=0:= by linarith
lemma zero_iff_sq_zero {a:ℝ}: a≠ 0 ↔ a^2 ≠ 0:=
begin
  split, all_goals{ contrapose! }, 
  { exact pow_eq_zero, },
  { simp, }
end
lemma recip_eq_imp_eq {a b c:ℝ} (h0: a ≠ 0) (h1: b ≠ 0) (h2: c≠ 0) (h3: c/a=c/b): a=b:=by field_simp * at *
lemma div_sq_sq {a b:ℝ} (h: b ≠ 0) : a^2/b^2 = (a/b)^2 :=by field_simp


lemma pell_solution_non_trivial {d:ℕ} (Y:ℤ) (f: ↥(S d) → ↥(A d)) (hd: nonsquare d) (N: ↥(A d)) (H4: (N:ℤ) ≠ 0) (x1 y1: ↥(S d)) (h11: (x1:ℤ ×ℤ).fst * (x1:ℤ ×ℤ).fst - ↑d * (x1:ℤ ×ℤ).snd * (x1:ℤ ×ℤ).snd = ↑N)
(h12: (y1:ℤ ×ℤ).fst * (y1:ℤ ×ℤ).fst - ↑d * (y1:ℤ ×ℤ).snd * (y1:ℤ ×ℤ).snd = ↑N) (hY: (x1:ℤ ×ℤ).fst * (y1:ℤ ×ℤ).snd - (y1:ℤ ×ℤ).fst * (x1:ℤ ×ℤ).snd = ↑N * Y) (x2: x1 ∈ f ⁻¹' {N}) (y2: y1 ∈ f ⁻¹' {N}) (hx: (⟨x1, x2⟩ : ↥(f⁻¹'{N})) ≠ ⟨y1, y2⟩ ): 1 ≤ |Y| :=
begin
  by_contra, push_neg at h,
      have q1: Y=0,
        {rw ← abs_eq_zero, apply zero_or_one (abs Y) (abs_nonneg Y) h, },
      rw q1 at hY,
      rw mul_zero at hY,
      rw sub_eq_zero at hY, 
      rw mul_assoc at h11 h12,
      repeat {rw ← pow_two at h11 h12},

      apply_fun (λ(a:ℤ), (a:ℝ)) at hY h11 h12,
      replace H4: ((N:ℤ):ℝ) ≠ 0,
        { norm_cast, simp [H4], },
      have q4: 1≤  (x1:ℤ×ℤ).snd,
        {cases x1, exact x1_property.1},
      replace q2: ((x1:ℤ×ℤ).snd:ℝ) ≠ 0, 
        {norm_cast, linarith}, 
      replace q4: 0 ≤ ((x1:ℤ×ℤ).snd:ℝ), 
        {norm_cast, linarith},

      have q5: 1 ≤   (y1:ℤ×ℤ).snd,
        {cases y1, exact y1_property.1},
      replace q3: ((y1:ℤ×ℤ).snd:ℝ) ≠ 0, 
        {norm_cast, linarith},
      replace q5: 0 ≤ ((y1:ℤ×ℤ).snd:ℝ), 
        {norm_cast, linarith},

      push_cast at h12 h11 hY,
      rw ← div_eq_div_iff q2 q3 at hY,
      rw ← div_left_inj' ((zero_iff_sq_zero).mp q2) at h11,
      rw ← div_left_inj' ((zero_iff_sq_zero).mp q3) at h12, 

      rw sub_div at h11 h12,

      have q6: ((x1:ℤ×ℤ).snd:ℝ)^2 = ((y1:ℤ×ℤ).snd:ℝ)^2,
        { apply recip_eq_imp_eq ((zero_iff_sq_zero).mp q2) ((zero_iff_sq_zero).mp q3) H4,
          rw ← h11, rw ← h12,
          repeat { rw div_sq_sq q2 },
          repeat { rw div_sq_sq q3 },
          rw hY,
          field_simp [q2, q3], },

      rw sq_eq_sq q4 q5 at q6,
      rw q6 at hY,
      rw div_left_inj' q3 at hY, 
      norm_cast at q6 hY,
      have q7: (⟨x1, x2⟩ : ↥(f⁻¹'{N}))  = ⟨y1, y2⟩,
        { apply subtype.eq, apply subtype.eq, apply prod.ext hY q6, },
      
      rw q7 at hx, exact hx rfl,
end

/--Theorem 3: If d is nonsquare then Pell's equation always has a nontrivial solution. --/
theorem exist_pell_solution {d:ℕ} (hd: nonsquare d): ∃ (x y:ℤ), x^2-d*y^2=1 ∧ 1 ≤ y:=
begin
  suffices goal:∃ (x y:ℤ),  (⟨x, y⟩ : ℤ√d).norm = 1 ∧ 1 ≤ y,
    { rcases goal with ⟨x, y, hy, hz⟩ , use x, use y, rw zsqrtd.norm_def at hy,split,
      { rw ← hy, ring_nf, },
      { assumption }},

  { have H1: ∀ (x: S d), ∃ (a:A d), (⟨x.val.1, x.val.2⟩ : ℤ√d).norm = (a:ℤ),
      { intros, use (⟨x.val.1, x.val.2⟩ : ℤ√d).norm, swap, 
      { simp, },
      { have h1:= inf_bounded_pairs x hd,
        assumption, }
      },
    haveI h2: fintype ↥(A d), 
      { exact set.finite.fintype (A_finite d) },
    choose f H2 using H1,
    haveI h3: infinite ↥(S d):= set.infinite_coe_iff.mpr (S_infinite hd),
    have H3:= fintype.exists_infinite_fiber f,
    rcases H3 with ⟨N,hN ⟩,
    have H4: (N:ℤ) ≠ 0,
      { rw set.infinite_coe_iff at hN, 
        have g1:=set.infinite.nonempty hN, 
        cases g1 with u gu, 
        replace gu:  f(u)=N:= gu,
        have g2:=H2 u,
        rw ← gu, 
        rw ← pell_to_norm at g2,
        rw ← g2, exact pell_ne_zero _ _ hd (show 1≤ u.val.snd, begin rcases u with ⟨u1, u2, u3⟩, assumption, end), },
    let B:= {x:ℤ | ∃ (v:ℤ), x=v%N},
    have h5: set.finite B,
      { refine bdd_below.finite_of_bdd_above _ _, 
      { use 0, intros w hw, cases hw, rw hw_h, exact int.mod_nonneg hw_w H4, },
      { use abs N, intros w hw, cases hw, rw hw_h, apply le_of_lt, exact int.mod_lt hw_w H4, }},
    let C:= B ×ˢ B,
    have h6: set.finite C,
      { exact set.finite.prod h5 h5, },

    have h7: ∀ ( t: ↥(f ⁻¹' {N})), ∃ (c: ↥C), (((t.1.val.1)%N :ℤ) ,((t.1.val.2)%N :ℤ)) =((c.1.1:ℤ), (c.1.2:ℤ)),
      { intro t, use (((t.1.val.1)%N :ℤ) ,((t.1.val.2)%N :ℤ)), split,
        { use (t.val.val.fst % ↑N), simp, },
        { use (t.val.val.snd % ↑N), simp, },
      }, 

    choose g h8 using h7,
    haveI hC: fintype ↥C,
      { exact set.finite.fintype h6 },
    have h9:= fintype.exists_ne_map_eq_of_infinite g,
    rcases h9 with ⟨ x, y, hx, hg ⟩,
    rcases x with ⟨x1, x2⟩, rcases y with ⟨y1, y2⟩,  
    
    have h8x:= h8 (⟨x1, x2⟩),
    apply_fun (λ(a: ↥C ),(a:ℤ ×ℤ)) at hg,
    norm_num at h8x,
    rw ← h8x at hg,
    have h8y:= h8 (⟨y1, y2⟩),
    norm_num at h8y,
    rw ← h8y at hg,
    rw prod.ext_iff at hg,
    dsimp at hg,
    cases hg with hg1 hg2, 
    rw remainder_to_modeq at hg1 hg2,
    have h10x: f x1 = N:=x2,
    have h10y: f y1 =N:= y2,
    apply_fun (λ(a: ↥(A d) ),(a:ℤ)) at h10x h10y, 
    have h11: (x1:ℤ×ℤ).fst*(x1:ℤ×ℤ).fst - d*(x1:ℤ×ℤ).snd*(x1:ℤ×ℤ).snd =N,
      { rw ← h10x, rw ← H2 x1, rw ← pell_to_norm, repeat {rw pow_two}, simp [mul_assoc], },
    have h12: (y1:ℤ×ℤ).fst*(y1:ℤ×ℤ).fst - d*(y1:ℤ×ℤ).snd*(y1:ℤ×ℤ).snd =N,
      { rw ← h10y, rw ← H2 y1, rw ← pell_to_norm, repeat {rw pow_two}, simp [mul_assoc], },
    
    
    have k1: (x1:ℤ×ℤ).fst*(y1:ℤ×ℤ).fst - d*(x1:ℤ×ℤ).snd*(y1:ℤ×ℤ).snd ≡ 0 [ZMOD (N:ℤ)],
      { have l1:= int.modeq.mul hg1 (show (y1:ℤ×ℤ).fst ≡ (y1:ℤ×ℤ).fst [ZMOD (N:ℤ)], by refl),
        replace l1:= int.modeq.sub l1 (show ↑d * (x1:ℤ×ℤ).snd * (y1:ℤ×ℤ).snd ≡ ↑d * (x1:ℤ×ℤ).snd * (y1:ℤ×ℤ).snd [ZMOD (N:ℤ)], by refl),
        apply int.modeq.trans l1, 
        replace h12:= eq_add_of_sub_eq h12,
        rw h12, rw (show (0:ℤ) =0+0, by refl), rw add_sub_assoc, apply int.modeq.add, 
        { refine int.mod_self, },
        { have l2:= int.modeq.mul hg2 (show (y1:ℤ×ℤ).snd ≡ (y1:ℤ×ℤ).snd [ZMOD (N:ℤ)], by refl), 
          apply int.modeq.add_right_cancel' ( d*(x1:ℤ×ℤ).snd * (y1:ℤ×ℤ).snd), ring_nf, rw pow_two, repeat {rw mul_assoc},
          apply int.modeq.mul (hg2.symm) (rfl), }},
    have k2:  (x1:ℤ×ℤ).fst*(y1:ℤ×ℤ).snd - (y1:ℤ×ℤ).fst*(x1:ℤ×ℤ).snd≡ 0 [ZMOD (N:ℤ)],
      { apply int.modeq.add_right_cancel' ((y1:ℤ×ℤ).fst * (x1:ℤ×ℤ).snd), ring_nf, symmetry' at hg2, apply int.modeq.mul hg2 hg1,  },
    rw int.modeq_zero_iff_dvd at k1 k2,
    cases k1 with X hX, 
    cases k2 with Y hY, 
    use X, use (abs Y),
    rw ← pell_to_norm,
    rw sq_abs,
    split,

    { rw ← mul_left_inj' H4, rw ← mul_left_inj' H4, rw mul_assoc, rw one_mul, repeat {rw ← pow_two},
      rw sub_mul, rw mul_assoc, repeat{rw sq_mul_sq}, rw mul_comm, nth_rewrite 2 mul_comm,
      rw ← hX, rw ← hY,
      nth_rewrite_rhs 0 pow_two, nth_rewrite 0 ← h11, rw ← h12,
      ring_nf, }, 

    { exact pell_solution_non_trivial Y f hd N H4 x1 y1 h11 h12 hY x2 y2 hx,
      
    },

  
  }
end
