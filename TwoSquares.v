Require Export Wilson.
Require Export Zsqrt.
Require Export ZdivExp.
Open Scope Z_scope.
 
Definition sum_of_two_squares :=
   fun p => exists a , exists b , p = a * a + b * b  .
 
Theorem two_squares_exists_mod:
 forall p a b,
 prime p ->
 ~ Zis_mod (b * b) 0 p ->
 Zis_mod (a * a + b * b) 0 p ->  (exists i , Zis_mod (i * i) (- 1) p ).
intros p a b Hp Hp1 Hp2.
assert (Ha1: 1 < p).
generalize (prime_le_2 p Hp); auto with zarith.
assert (Ha2: rel_prime b p).
apply rel_prime_sym; apply prime_rel_prime; auto with zarith.
intros [x Hx]; case Hp1; exists ((x * x) * p).
subst b; ring.
case (Zis_mod_rel_prime_inverse b p); auto with zarith.
intros b' [Hb1 [Hb2 Hb3]].
exists (a * b').
apply Zis_mod_cancel with b; auto with zarith.
apply Zis_mod_cancel with b; auto with zarith.
apply Zis_mod_trans with ((1 * 1) * (a * a)); auto with zarith.
replace (b * (b * ((a * b') * (a * b')))) with (((b * b') * (b * b')) * (a * a));
 (try ring).
(repeat apply Zis_mod_mult); auto.
apply Zis_mod_ref.
apply Zis_mod_ref.
red.
replace ((1 * 1) * (a * a) - b * (b * - 1)) with ((a * a + b * b) - 0);
 auto with zarith.
ring.
Qed.
 
Theorem two_squares_interval:
 forall p a b, prime p -> p = a * a + b * b ->  ( 0 < Zabs a < p ).
intros p a b Hp; rewrite (Zabs_square a); rewrite (Zabs_square b); intros Hp1.
assert (Hp2: 1 < p).
generalize (prime_le_2 p Hp); auto with zarith.
case (Zle_lt_or_eq 0 (Zabs a)); auto with zarith; intros Hza1.
assert (Ha1: 0 < Zabs a * Zabs a).
replace 0 with (0 * Zabs a); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
case (Zle_lt_or_eq 0 (Zabs b)); auto with zarith; intros Hza2.
assert (Ha2: 0 < Zabs b * Zabs b).
replace 0 with (0 * Zabs b); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
split; auto.
replace (Zabs a) with (1 * Zabs a + 0 * 0); auto with zarith.
apply Zle_lt_trans with (Zabs a * Zabs a + 0 * 0); auto with zarith.
contradict Hp; rewrite Hp1; rewrite <- Hza2; simpl.
rewrite Zplus_0_r; apply square_not_prime.
contradict Hp; rewrite Hp1; rewrite <- Hza1; simpl.
apply square_not_prime.
Qed.
 
Theorem two_squares_sqrt_interval:
 forall p a b, prime p -> p = a * a + b * b ->  ( 0 < Zabs a <= Zsqrt_plain p ).
intros p a b Hp Hp1; split.
case two_squares_interval with ( 2 := Hp1 ); auto.
rewrite <- (Zsqrt_square_id (Zabs a)); auto with zarith.
apply Zsqrt_le; auto.
split; auto with zarith.
rewrite Hp1; rewrite (Zabs_square a); rewrite (Zabs_square b); auto with zarith.
apply Zle_trans with (Zabs a * Zabs a + 0 * Zabs b); auto with zarith.
Qed.
 
Theorem two_squares_exists_mod_cor:
 forall p,
 prime p -> sum_of_two_squares p ->  (exists i , Zis_mod (i * i) (- 1) p ).
intros p Hp [a [b Hp1]]; rewrite (Zabs_square a) in Hp1;
 rewrite (Zabs_square b) in Hp1.
assert (Hp2: 1 < p).
generalize (prime_le_2 p Hp); auto with zarith.
apply (two_squares_exists_mod p (Zabs b) (Zabs a)); auto with zarith.
intros Hu; absurd (Zabs a * Zabs a = 0); auto with zarith.
intros Hp3; contradict Hp; rewrite Hp1; rewrite Hp3; simpl;
 apply square_not_prime.
rewrite <- (Zmod_def_small (Zabs a * Zabs a) p); auto with zarith.
rewrite <- (Zmod_def_small 0 p); auto with zarith.
apply Zis_mod_def_inv; auto with zarith.
case (two_squares_interval p a b); auto with zarith.
rewrite Hp1; (repeat rewrite <- Zabs_square); auto.
intros H1 H2; split; auto with zarith.
case (two_squares_interval p b a); auto with zarith.
rewrite Hp1; (repeat rewrite <- Zabs_square); auto with zarith.
intros H3 H4.
apply Zle_lt_trans with (Zabs a * Zabs a + 0 * Zabs b); auto with zarith.
rewrite Hp1; auto with zarith.
apply Zplus_lt_compat_l; auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
rewrite Hp1; exists 1; auto with zarith.
Qed.
 
Definition prod2 :=
   fun x1 y1 x2 y2 =>
   list_prod
    (progression Zsucc x1 (Zabs_nat (y1 - x1)))
    (progression Zsucc x2 (Zabs_nat (y2 - x2))).
 
Theorem in_prod2_inv:
 forall x1 y1 x2 y2 x3 y3,
 x1 <= y1 ->
 x2 <= y2 ->
 In (x3, y3) (prod2 x1 y1 x2 y2) ->  ( x1 <= x3 < y1 ) /\ ( x2 <= y3 < y2 ).
intros x1 y1 x2 y2 x3 y3 H1 H2 H3.
case (in_list_prod_inv _ _ _ _ _ H3); auto.
intros a1 [b1 [H4 [H5 H6]]]; injection H4; clear H4; intros; subst a1; subst b1.
split; split.
apply Zprogression_le_init with ( 1 := H5 ).
rewrite <- (Z_of_nat_abs_le x1 y1); auto;
 apply Zprogression_le_end with ( 1 := H5 ).
apply Zprogression_le_init with ( 1 := H6 ).
rewrite <- (Z_of_nat_abs_le x2 y2); auto;
 apply Zprogression_le_end with ( 1 := H6 ).
Qed.
 
Theorem prod_Z_surjective:
 forall f x1 y1 x2 y2 x3 y3,
 x1 < y1 ->
 x2 < y2 ->
 x3 < y3 ->
 (forall x y, ( x1 <= x < y1 ) -> ( x2 <= y < y2 ) ->  ( x3 <= f x y < y3 )) ->
 y3 - x3 < (y1 - x1) * (y2 - x2) ->
  (exists x ,
   exists y ,
   exists z ,
   exists t ,
   (( x1 <= x < y1 ) /\ ( x1 <= y < y1 )) /\
   ((( x2 <= z < y2 ) /\ ( x2 <= t < y2 )) /\
    ((x, z) <> (y, t) /\ f x z = f y t))    ).
intros f x1 y1 x2 y2 x3 y3 H1 H2 H3 H4 H5.
case
 (incl_length_repetition
   _ Z_eq_dec (map (fun p => f (fst p) (snd p)) (prod2 x1 y1 x2 y2))
   (progression Zsucc x3 (Zabs_nat (y3 - x3)))).
intros a Ha.
case in_map_inv with ( 1 := Ha ); intros a1; case a1; simpl; clear a1;
 intros a1 b1 [Ha1 Hb1].
case (in_list_prod_inv _ _ _ _ _ Ha1).
intros c1 [d1 [Hd1 [Hd2 Hd3]]].
subst a.
injection Hd1; clear Hd1; intros tmp1 tmp2; subst c1; subst d1.
apply in_Zprogression; auto.
rewrite Z_of_nat_abs_le; auto with zarith.
apply H4; auto.
split.
apply Zprogression_le_init with ( 1 := Hd2 ).
rewrite <- (Z_of_nat_abs_le x1 y1); auto with zarith.
apply Zprogression_le_end with ( 1 := Hd2 ).
split.
apply Zprogression_le_init with ( 1 := Hd3 ).
rewrite <- (Z_of_nat_abs_le x2 y2); auto with zarith.
apply Zprogression_le_end with ( 1 := Hd3 ).
rewrite length_map; unfold prod2; rewrite length_list_prod;
 (repeat rewrite length_progression).
red; apply inj_le_inv.
rewrite inj_mult; rewrite inj_S; (repeat rewrite Z_of_nat_Zabs_nat);
 auto with zarith.
intros a [l1 [l2 [l3 [Hl1 Hl2]]]].
case (same_length_ex _ _ a l1 (app l2 (cons a l3)) (prod2 x1 y1 x2 y2)).
simpl in Hl1 |-; rewrite <- Hl1; apply length_map.
intros l4 [l5 [[a1 b1] [Hg1 [Hg2 Hg3]]]].
generalize Hl1; rewrite Hg3.
intros tmp; (case map_length_decompose with ( 2 := tmp ); clear tmp); auto.
intros Hh1 Hh2.
case (same_length_ex _ _ a l2 l3 l5); auto.
intros l6 [l7 [[c1 d1] [Hj1 [Hj2 Hj3]]]].
simpl in Hh2 |-; injection Hh2; clear Hh2.
intros Hh2 Hh3; subst a.
rewrite Hj3 in Hh2; case map_length_decompose with ( 2 := Hh2 ); clear Hh2; auto.
intros Hl3 Hl4.
exists a1; exists c1; exists b1; exists d1.
case (in_prod2_inv x1 y1 x2 y2 a1 b1); auto with zarith.
rewrite Hg3; auto with datatypes.
intros Hr1 Hr2.
case (in_prod2_inv x1 y1 x2 y2 c1 d1); auto with zarith.
rewrite Hg3; rewrite Hj3; auto with datatypes.
apply in_or_app; right; auto with datatypes.
intros Hr3 Hr4.
assert (ulist (cons (a1, b1) (app l6 (cons (c1, d1) l7)))).
rewrite <- Hj3.
apply ulist_app_inv_r with l4; auto.
rewrite <- Hg3; auto.
unfold prod2; apply ulist_list_prod; apply ulist_Zprogression.
repeat (split; auto).
intros HH; injection HH; clear HH; intros; subst c1; subst d1.
absurd (In (a1, b1) (app l6 (cons (a1, b1) l7))); auto with datatypes.
inversion H; auto.
simpl in Hl4 |-; injection Hl4; auto.
Qed.
 
Theorem two_squares_mod_exists_sum:
 forall p i, prime p -> Zis_mod (i * i) (- 1) p ->  sum_of_two_squares p.
intros p i H1 H2.
assert (H3: 1 < p).
inversion H1; auto.
assert (H4: 0 <= Zsqrt_plain p).
apply Zsqrt_plain_is_pos; auto with zarith.
case
 (prod_Z_surjective
   (fun x y => Zmod (x + i * y) p) 0 (Zsqrt_plain p + 1) 0 (Zsqrt_plain p + 1) 0
   p); auto with zarith.
intros x y _ _; apply Z_mod_lt; auto with zarith.
repeat rewrite Zminus_0_r.
case (Zsqrt_interval p); auto with zarith.
intros x1 [x2 [y1 [y2 [[Ha1 Hb1] [[Ha2 Hb2] [Ha3 Ha4]]]]]].
exists (Zabs (x1 - x2)); exists (Zabs (y2 - y1)).
assert (Hc:
 Zis_mod (Zabs (x1 - x2) * Zabs (x1 - x2) + Zabs (y2 - y1) * Zabs (y2 - y1)) 0 p).
repeat rewrite <- Zabs_square.
apply Zis_mod_trans
     with ((x1 - x2) * (x1 - x2) - ((i * i) * (y2 - y1)) * (y2 - y1)).
replace ((x1 - x2) * (x1 - x2) + (y2 - y1) * (y2 - y1))
     with ((x1 - x2) * (x1 - x2) - (- 1 * (y2 - y1)) * (y2 - y1)); (try ring).
apply Zis_mod_minus; auto.
apply Zis_mod_ref; auto.
(repeat (apply Zis_mod_mult || apply Zis_mod_ref)); auto.
apply Zis_mod_sym; auto.
apply Zis_mod_minus_0; auto.
replace (((i * i) * (y2 - y1)) * (y2 - y1))
     with ((i * (y2 - y1)) * (i * (y2 - y1))); (try ring).
assert (Hc: Zis_mod (x1 - x2) (i * (y2 - y1)) p).
replace (x1 - x2) with ((x1 - x2) + - 1 * 0); auto with zarith.
replace (i * (y2 - y1)) with ((x1 - x2) + - 1 * ((x1 + i * y1) - (x2 + i * y2)));
 (try ring).
apply Zis_mod_plus; auto.
apply Zis_mod_ref; auto.
(repeat (apply Zis_mod_mult || apply Zis_mod_ref)); auto.
apply Zis_mod_sym; apply Zis_mod_minus_0.
apply Zis_mod_def; auto with zarith.
apply Zis_mod_mult; auto.
assert (Hc1:
  0 <= Zabs (x1 - x2) * Zabs (x1 - x2) + Zabs (y2 - y1) * Zabs (y2 - y1) < 2 * p
 ).
split; auto with zarith.
replace (2 * p) with (p + p); auto with zarith.
apply Zplus_lt_compat; auto with zarith.
apply Zle_lt_trans with (Zsqrt_plain p * Zsqrt_plain p); auto with zarith.
assert (Hc1: Zabs (x1 - x2) <= Zsqrt_plain p); auto with zarith.
case (Zle_or_lt x1 x2); intros Hc1.
apply Zle_trans with x2; auto with zarith.
rewrite Zabs_non_eq; auto with zarith.
apply Zle_trans with x1; auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply Zmult_le_compat; auto with zarith.
case (Zsqrt_interval p); auto with zarith.
intros Hc1 Hc2; case Zle_lt_or_eq with ( 1 := Hc1 ); auto.
intros Hc3; contradict H1; rewrite <- Hc3; apply square_not_prime.
apply Zle_lt_trans with (Zsqrt_plain p * Zsqrt_plain p); auto with zarith.
assert (Hc1: Zabs (y2 - y1) <= Zsqrt_plain p); auto with zarith.
case (Zle_or_lt y2 y1); intros Hc1.
rewrite Zabs_non_eq; auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply Zmult_le_compat; auto with zarith.
case (Zsqrt_interval p); auto with zarith.
intros Hc1 Hc2; case Zle_lt_or_eq with ( 1 := Hc1 ); auto.
intros Hc3; contradict H1; rewrite <- Hc3; apply square_not_prime.
case Hc1; clear Hc1; intros Hc1 Hc2.
case Zle_lt_or_eq with ( 1 := Hc1 ); clear Hc1; intros Hc1.
case Hc.
rewrite Zminus_0_r; intros q Hq; rewrite Hq; rewrite Hq in Hc1;
 rewrite Hq in Hc2; clear Hq.
assert (Hc3:  0 < q < 2 ).
split; intros; apply Zmult_gt_0_lt_reg_r with p; auto with zarith.
case (Zle_lt_or_eq 1 q); auto with zarith.
intros Hc4; rewrite <- Hc4; auto with zarith.
absurd (0 < Zabs (x1 - x2) * Zabs (x1 - x2) + Zabs (y2 - y1) * Zabs (y2 - y1)).
rewrite <- Hc1; auto with zarith.
replace 0 with (0 * Zabs (x1 - x2) + 0 * Zabs (y2 - y1)); auto with zarith.
cut (x1 = x2 \/ 0 < Zabs (x1 - x2)).
intros [Hc3|Hc3].
cut (y1 = y2 \/ 0 < Zabs (y2 - y1)).
intros [Hc4|Hc4].
case Ha3; apply f_equal2 with ( f := @pair Z Z ); auto.
apply Zplus_le_lt_compat; auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
case (Zle_or_lt y1 y2); intros He.
case Zle_lt_or_eq with ( 1 := He ); intros He1; auto.
rewrite Zabs_eq; auto with zarith.
rewrite Zabs_non_eq; auto with zarith.
apply Zplus_lt_le_compat; auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
case (Zle_or_lt x1 x2); intros Hd.
case Zle_lt_or_eq with ( 1 := Hd ); intros Hd1; auto.
rewrite Zabs_non_eq; auto with zarith.
rewrite Zabs_eq; auto with zarith.
Qed.
 
Theorem two_squares_unique:
 forall a b c d p,
 prime p ->
 0 <= a ->
 0 <= b ->
 0 <= c ->
 0 <= d ->
 p = a * a + b * b -> p = c * c + d * d ->  a = c /\ b = d \/ a = d /\ b = c.
intros a b c d p H1 H2 H3 H4 H5 H6 H7.
assert (Hp: 1 < p).
inversion H1; auto.
assert (Hs: Zsqrt_plain p * Zsqrt_plain p < p).
case (Zsqrt_interval p); auto with zarith; intros tmp;
 (case Zle_lt_or_eq with ( 1 := tmp ); auto); intros tmp1 tmp2; contradict H1;
 rewrite <- tmp1; apply square_not_prime.
case Zle_lt_or_eq with ( 1 := H2 ); clear H2; intros H2.
2:contradict H1; rewrite H6; replace (a * a + b * b) with (b * b);
   rewrite <- H2 || apply square_not_prime; auto with zarith.
case Zle_lt_or_eq with ( 1 := H3 ); clear H3; intros H3.
2:contradict H1; rewrite H6; replace (a * a + b * b) with (a * a);
   rewrite <- H3 || apply square_not_prime; auto with zarith.
case Zle_lt_or_eq with ( 1 := H4 ); clear H4; intros H4.
2:contradict H1; rewrite H7; replace (c * c + d * d) with (d * d);
   rewrite <- H4 || apply square_not_prime; auto with zarith.
case Zle_lt_or_eq with ( 1 := H5 ); clear H5; intros H5.
2:contradict H1; rewrite H7; replace (c * c + d * d) with (c * c);
   rewrite <- H5 || apply square_not_prime; auto with zarith.
case (two_squares_sqrt_interval p a b); auto with zarith; rewrite Zabs_eq;
 auto with zarith; intros Hc1 Hc2.
case (two_squares_sqrt_interval p b a); auto with zarith; rewrite Zabs_eq;
 auto with zarith; intros Hc3 Hc4.
case (two_squares_sqrt_interval p c d); auto with zarith; rewrite Zabs_eq;
 auto with zarith; intros Hc5 Hc6.
case (two_squares_sqrt_interval p d c); auto with zarith; rewrite Zabs_eq;
 auto with zarith; intros Hc7 Hc8.
case (prime_mult p H1 (a * d - b * c) (a * d + b * c)); (try intros Ha1).
exists (d * d - b * b).
apply trans_equal with (d * (d * p) - b * (b * p)); (try (ring; fail)).
pattern p at 1; rewrite H6; rewrite H7; ring.
left; assert (Hb1:  - p < a * d - b * c < p ).
split.
apply Zle_lt_trans with (0 * d - b * c); auto with zarith.
replace (0 * d - b * c) with (- (b * c)); auto with zarith.
cut (b * c <= p); auto with zarith.
apply Zle_trans with (Zsqrt_plain p * Zsqrt_plain p); auto with zarith.
apply Zmult_le_compat; auto with zarith.
unfold Zminus; apply Zplus_lt_compat_r; auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
apply Zle_lt_trans with (a * d - 0 * c); auto with zarith.
unfold Zminus; apply Zplus_le_compat; auto with zarith.
cut (0 * c <= b * c); auto with zarith.
replace (a * d - 0 * c) with (a * d); auto with zarith.
apply Zle_lt_trans with (Zsqrt_plain p * Zsqrt_plain p); auto with zarith.
apply Zmult_le_compat; auto with zarith.
case Ha1; clear Ha1; intros q Ha1.
assert (Hb2: q = 0).
assert (Hb3:  - 1 < q < 1 ).
split; intros; apply Zmult_gt_0_lt_reg_r with p; auto with zarith.
case (Zle_lt_or_eq 0 q); auto with zarith.
assert (Hb3: a * d = b * c).
apply Zminus_eq; rewrite Ha1; rewrite Hb2; auto with zarith.
clear q Ha1 Hb1 Hb2.
assert (Hb1: Zdivide a c).
apply Gauss with b; auto with zarith.
exists d; auto.
rewrite (Zmult_comm d); auto with zarith.
red.
assert (Zdivide (Zgcd a b) p).
rewrite H6; apply Zdivide_plus_r; auto with zarith.
apply Zdivide_trans with a; auto with zarith.
generalize (Zgcd_is_gcd a b); intros tmp; inversion tmp; auto.
apply Zdivide_trans with b; auto with zarith.
generalize (Zgcd_is_gcd a b); intros tmp; inversion tmp; auto.
case (Zle_lt_or_eq 0 (Zgcd a b)); auto with zarith.
generalize (Zgcd_is_pos a b); auto with zarith.
intros HH1; case (Zle_lt_or_eq 1 (Zgcd a b)); auto with zarith.
intros HH2; contradict H; apply prime_inv_def; auto with zarith.
split; auto.
apply Zle_lt_trans with a; auto with zarith.
apply Zdivide_le; auto with zarith.
generalize (Zgcd_is_gcd a b); intros tmp; inversion tmp; auto.
apply Zle_lt_trans with ( 1 := Hc2 ).
apply Zle_lt_trans with (Zsqrt_plain p * Zsqrt_plain p); auto with zarith.
apply Zle_trans with (1 * Zsqrt_plain p); auto with zarith.
intros tmp; rewrite tmp; apply Zgcd_is_gcd.
intros HH1.
generalize (Zgcd_is_gcd a b); intros tmp; inversion tmp; auto.
case H0; intros q; rewrite <- HH1.
intros HH2; contradict H2; rewrite HH2; auto with zarith.
case Hb1; clear Hb1; intros k Hb1.
assert (Hb2: d = k * b).
apply Zmult_reg_l with a; auto with zarith.
apply trans_equal with ( 1 := Hb3 ).
rewrite Hb1; ring.
assert (Hb4: k * k = 1).
apply Zmult_reg_l with p; auto with zarith.
pattern p at 1; rewrite H6.
apply trans_equal with ((k * a) * (k * a) + (k * b) * (k * b)).
ring.
rewrite <- Hb1; rewrite <- Hb2; auto with zarith.
rewrite Hb1; rewrite Hb2; replace k with 1; auto with zarith.
case (Zmult_1_inversion_l k k); auto.
intros tmp; contradict H4; rewrite Hb1; rewrite tmp; auto with zarith.
right; assert (Hb1: a * c = b * d).
case Ha1; clear Ha1; intros q Ha1.
assert (Hb2: q = 1).
assert (Hb3:  0 < q < 2 ).
split; intros; apply Zmult_gt_0_lt_reg_r with p; auto with zarith.
rewrite <- Ha1; auto with zarith.
replace (0 * p) with (0 * d + 0 * c); auto with zarith.
apply Zplus_lt_compat; apply Zmult_lt_compat_r; auto with zarith.
replace (2 * p) with (p + p); auto with zarith.
rewrite <- Ha1; apply Zplus_lt_compat;
 apply Zle_lt_trans with (Zsqrt_plain p * Zsqrt_plain p); auto with zarith.
apply Zle_trans with (Zsqrt_plain p * d); auto with zarith.
apply Zle_trans with (Zsqrt_plain p * c); auto with zarith.
case (Zle_lt_or_eq 1 q); auto with zarith.
rewrite Hb2 in Ha1; rewrite Zmult_1_l in Ha1.
apply Zminus_eq; case ((fun x => Zmult_integral x x) (a * c - b * d)); auto.
apply Zplus_reg_l with (p * p); auto with zarith.
pattern p at 1 2; rewrite <- Ha1; pattern p at 1; rewrite H7; rewrite H6; ring.
assert (Hb2: Zdivide a d).
apply Gauss with b; auto with zarith.
exists c; auto.
rewrite (Zmult_comm c); auto with zarith.
red.
assert (Zdivide (Zgcd a b) p).
rewrite H6; apply Zdivide_plus_r; auto with zarith.
apply Zdivide_trans with a; auto with zarith.
generalize (Zgcd_is_gcd a b); intros tmp; inversion tmp; auto.
apply Zdivide_trans with b; auto with zarith.
generalize (Zgcd_is_gcd a b); intros tmp; inversion tmp; auto.
case (Zle_lt_or_eq 0 (Zgcd a b)); auto with zarith.
generalize (Zgcd_is_pos a b); auto with zarith.
intros HH1; case (Zle_lt_or_eq 1 (Zgcd a b)); auto with zarith.
intros HH2; contradict H; apply prime_inv_def; auto with zarith.
split; auto.
apply Zle_lt_trans with a; auto with zarith.
apply Zdivide_le; auto with zarith.
generalize (Zgcd_is_gcd a b); intros tmp; inversion tmp; auto.
apply Zle_lt_trans with ( 1 := Hc2 ).
apply Zle_lt_trans with (Zsqrt_plain p * Zsqrt_plain p); auto with zarith.
apply Zle_trans with (1 * Zsqrt_plain p); auto with zarith.
intros tmp; rewrite tmp; apply Zgcd_is_gcd.
intros HH1.
generalize (Zgcd_is_gcd a b); intros tmp; inversion tmp; auto.
case H0; intros q; rewrite <- HH1.
intros HH2; contradict H2; rewrite HH2; auto with zarith.
case Hb2; clear Hb2; intros k Hb2.
assert (Hb3: c = k * b).
apply Zmult_reg_l with a; auto with zarith.
apply trans_equal with ( 1 := Hb1 ).
rewrite Hb2; ring.
assert (Hb4: k * k = 1).
apply Zmult_reg_l with p; auto with zarith.
pattern p at 1; rewrite H6.
apply trans_equal with ((k * a) * (k * a) + (k * b) * (k * b)).
ring.
rewrite <- Hb2; rewrite <- Hb3; auto with zarith.
rewrite Hb3; rewrite Hb2; replace k with 1; auto with zarith.
case (Zmult_1_inversion_l k k); auto.
intros tmp; contradict H4; rewrite Hb3; rewrite tmp; auto with zarith.
Qed.
 
Theorem two_square_mod_exists_2: Zis_mod (1 * 1) (- 1) 2.
exists 1; auto with zarith.
Qed.
 
Theorem two_square_mod_exists_1_mod4:
 forall p,
 prime p ->
 Zis_mod p 1 4 ->
  Zis_mod (Zfact (Zdiv (p - 1) 2) * Zfact (Zdiv (p - 1) 2)) (- 1) p.
intros p Hp Hp1.
case Hp1; clear Hp1; intros q Hp1.
replace ((p - 1) / 2) with (2 * q).
2:rewrite Hp1; replace (q * 4) with ((2 * q) * 2); (try rewrite Z_div_mult);
   auto with zarith.
assert (Hp2: 1 < p).
inversion Hp; auto.
assert (Hp3: 0 < q).
case (Zle_lt_or_eq 0 q); auto with zarith.
apply Zis_mod_trans with ( 2 := wilson p Hp ).
rewrite Hp1.
assert (Hp4: 1 < 2 * q).
apply Zle_lt_trans with (1 * q); auto with zarith.
unfold Zfact; rewrite (Zprod_split_up 1 (2 * q) (q * 4)); auto with zarith.
replace (Zprod (2 * q + 1) (q * 4) (fun (x : Z) => x))
     with (Zprod 1 (2 * q) (fun (x : Z) => 2 * q + x)).
apply Zis_mod_def; auto with zarith.
(repeat rewrite (fun x y z => Zmod_mult (Zprod x y z))); auto with zarith.
apply f_equal2 with ( f := Zmod ); auto.
apply f_equal2 with ( f := Zmult ); auto.
apply trans_equal
     with (Zprod 1 (2 * q) (fun (x : Z) => - 1 * ((2 * q + 1) - x)) mod p).
apply f_equal2 with ( f := Zmod ); auto.
rewrite <- (Zprod_mult 1 (2 * q) (fun x => - 1) (fun x => (2 * q + 1) - x)).
rewrite (Zprod_c (- 1)); auto with zarith.
replace (Zpower (- 1) ((1 + 2 * q) - 1)) with 1.
rewrite Zmult_1_l.
unfold Zprod; rewrite Zle_imp_le_bool; auto with zarith.
rewrite <- (iter_map
             _ _ _ 1 (fun (x : Z) => x) Zmult (fun (x : Z) => (2 * q + 1) - x)).
apply iter_permutation; auto with zarith.
apply permutation_trans
     with (rev (progression Zsucc 1 (Zabs_nat ((1 + 2 * q) - 1)))).
apply permutation_sym; apply permutation_rev.
rewrite Zprogression_opp; auto.
replace ((1 + 2 * q) - 1) with (2 * q); auto with zarith.
replace (1 + Z_of_nat (pred (Zabs_nat (2 * q)))) with (2 * q); auto with zarith.
pattern (2 * q) at 1 3; rewrite <- (Z_of_nat_Zabs_nat (2 * q)).
cut (exists c , c = Zabs_nat (2 * q) ).
intros [c Hc]; pattern (Zabs_nat (2 * q)) at 1 3; rewrite <- Hc.
cut (le (Zabs_nat (2 * q)) c).
generalize c; elim (Zabs_nat (2 * q)); auto; clear c Hc.
intros n Rec c Hc.
repeat rewrite Zprogression_end.
rewrite map_app.
rewrite Zprogression_pred_end.
apply permutation_app_comp; auto with zarith.
replace (Z_of_nat c - Z_of_nat n) with ((Z_of_nat c + 1) - (1 + Z_of_nat n));
 apply permutation_refl || ring.
rewrite Hc; auto with arith.
exists (Zabs_nat (2 * q)); auto.
auto with zarith.
pattern (2 * q) at 2; replace (2 * q) with (Zsucc (Zpred (2 * q)));
 auto with zarith.
rewrite Zabs_nat_Zsucc; auto with zarith.
rewrite <- pred_Sn; rewrite Z_of_nat_Zabs_nat; auto with zarith.
unfold Zpred; ring.
unfold Zpred; auto with zarith.
unfold Zpred; auto with zarith.
unfold Zsucc, Zpred; auto with zarith.
replace ((1 + 2 * q) - 1) with (2 * q); auto with zarith.
replace (2 * q) with (q + q); auto with zarith.
rewrite Zpower_exp; auto with zarith.
rewrite Zabs_square; rewrite Zpower_Zabs; auto with zarith.
replace (Zabs (- 1)) with 1; (repeat rewrite Zpower_1); auto with zarith.
unfold Zprod; (rewrite Zle_imp_le_bool; auto with zarith).
elim (Zabs_nat ((1 + 2 * q) - 1)); auto.
intros n Rec.
(repeat rewrite Zprogression_end); auto with zarith.
(repeat rewrite iter_app); auto with zarith.
rewrite (Zmod_mult
          (iter
            1 (fun (x : Z) => - 1 * ((2 * q + 1) - x)) Zmult
            (progression Zsucc 1 n))); auto with zarith.
rewrite (Zmod_mult
          (iter 1 (fun (x : Z) => 2 * q + x) Zmult (progression Zsucc 1 n)));
 auto with zarith.
apply f_equal2 with ( f := Zmod ); auto.
apply f_equal2 with ( f := Zmult ); auto.
change
 (Zmod ((- 1 * ((2 * q + 1) - (1 + Z_of_nat n))) * 1) p =
  Zmod ((2 * q + (1 + Z_of_nat n)) * 1) p).
apply Zis_mod_def_inv; auto with zarith.
exists (- 1); replace p with (q * 4 + 1); [idtac | rewrite <- Hp1]; ring.
replace (q * 4) with (2 * q + 2 * q); (try ring).
unfold Zprod; ((repeat rewrite Zle_imp_le_bool); auto with zarith).
rewrite <- (iter_map _ _ _ 1 (fun (x : Z) => x) Zmult (fun (x : Z) => 2 * q + x));
 auto.
apply f_equal4 with ( f := @iter Z Z ); auto.
replace ((1 + 2 * q) - 1) with (2 * q); auto with zarith.
replace ((1 + (2 * q + 2 * q)) - (2 * q + 1)) with (2 * q); auto with zarith.
elim (Zabs_nat (2 * q)); auto with zarith.
intros n Rec.
(repeat rewrite Zprogression_end); auto with zarith.
(repeat rewrite map_app); auto with zarith.
apply f_equal2 with ( f := @app Z ); auto.
change
 (cons (2 * q + (1 + Z_of_nat n)) nil = cons ((2 * q + 1) + Z_of_nat n) nil).
apply f_equal2 with ( f := @cons Z ); auto with zarith.
Qed.
 
Theorem prime_case_4:
 forall p, prime p ->  p = 2 \/ (Zis_mod p 1 4 \/ Zis_mod p 3 4).
intros p Hp.
case (Z_mod_lt p 4); auto with zarith.
intros H2 H3; case Zle_lt_or_eq with ( 1 := H2 ); clear H2; intros H2.
case (Zle_lt_or_eq 1 (p mod 4)); auto with zarith; clear H2; intros H2.
case (Zle_lt_or_eq 2 (p mod 4)); auto with zarith; clear H2; intros H2.
case (Zle_lt_or_eq 3 (p mod 4)); auto with zarith; clear H2; intros H2.
rewrite H2; right; right; apply Zis_mod_mod; auto with zarith.
left; case (Zle_lt_or_eq 2 p); auto with zarith.
inversion Hp; auto with zarith.
intros H4; case (prime_inv_def p 2); auto with zarith.
rewrite (Z_div_mod_eq p 4); auto with zarith.
rewrite <- H2; exists (2 * (p / 4) + 1); ring.
rewrite H2; right; left; apply Zis_mod_mod; auto with zarith.
absurd (Zdivide 4 p).
intros [q Hq].
case (Zle_lt_or_eq 0 q); auto with zarith.
apply Zmult_le_reg_r with 4; auto with zarith.
rewrite <- Hq; inversion Hp; auto with zarith.
intros H4; absurd (Zdivide 2 p).
apply prime_inv_def; auto with zarith.
exists (2 * q); rewrite Hq; auto with zarith.
intros H4; contradict Hp; rewrite Hq; rewrite <- H4.
rewrite Zmult_0_l.
apply not_prime_0.
exists (Zdiv p 4).
pattern p at 1; rewrite (Z_div_mod_eq p 4); auto with zarith.
Qed.
 
Theorem two_squares_mod_inv:
 forall p i, prime p -> Zis_mod (i * i) (- 1) p ->  p = 2 \/ Zis_mod p 1 4.
intros p i Hp H1.
generalize (prime_case_4 p Hp); intros [H2|[H2|H2]]; auto.
case two_squares_mod_exists_sum with ( 2 := H1 ); auto with zarith.
intros a [b Hab].
absurd (Zmod p 4 = Zmod 3 4).
rewrite Hab.
rewrite Zmod_plus_eq; auto with zarith.
rewrite (Zmod_mult a); (try rewrite (Zmod_mult b)); auto with zarith.
assert (Ha: a mod 4 = 0 \/ (a mod 4 = 1 \/ (a mod 4 = 2 \/ a mod 4 = 3))).
case (Z_mod_lt a 4); auto with zarith; intros Ha Ha1.
case Zle_lt_or_eq with ( 1 := Ha ); clear Ha; intros Ha; auto.
case (Zle_lt_or_eq 1 (a mod 4)); auto with zarith; clear Ha; intros Ha; auto.
case (Zle_lt_or_eq 2 (a mod 4)); auto with zarith; clear Ha; intros Ha; auto.
assert (Hb: b mod 4 = 0 \/ (b mod 4 = 1 \/ (b mod 4 = 2 \/ b mod 4 = 3))).
case (Z_mod_lt b 4); auto with zarith; intros Hb Hb1.
case Zle_lt_or_eq with ( 1 := Hb ); clear Hb; intros Hb; auto.
case (Zle_lt_or_eq 1 (b mod 4)); auto with zarith; clear Hb; intros Hb; auto.
case (Zle_lt_or_eq 2 (b mod 4)); auto with zarith; clear Hb; intros Hb; auto.
generalize Ha Hb; intros [HH1|[HH1|[HH1|HH1]]]; intros [HL1|[HL1|[HL1|HL1]]];
 (repeat rewrite HH1); (repeat rewrite HL1); (intros; (try discriminate)).
apply Zis_mod_def_inv; auto with zarith.
Qed.
 
Theorem two_squares_case:
 forall p, prime p -> sum_of_two_squares p ->  p = 2 \/ Zis_mod p 1 4.
intros p H1 [a [b H2]].
case (two_squares_exists_mod_cor p); auto.
exists a; exists b; auto.
intros i Hi; apply two_squares_mod_inv with ( 2 := Hi ); auto.
Qed.
 
Theorem two_squares_exists:
 forall p, prime p -> p = 2 \/ Zis_mod p 1 4 ->  sum_of_two_squares p.
intros p Hp [H1|H1].
apply two_squares_mod_exists_sum with 1; auto.
subst p; apply two_square_mod_exists_2; auto.
apply two_squares_mod_exists_sum with (Zfact (Zdiv (p - 1) 2)); auto.
apply two_square_mod_exists_1_mod4; auto.
Qed.
 
Theorem two_squares_comp:
 forall n m,
 sum_of_two_squares n -> sum_of_two_squares m ->  sum_of_two_squares (n * m).
intros n m [a [b Hn]] [c [d Hm]].
exists (a * c - b * d); exists (a * d + b * c).
rewrite Hm; rewrite Hn; ring.
Qed.
 
Theorem not_prime_prime_divide:
 forall n,
 (1 < n)%Z ->
 ~ prime n ->  (exists p , ( 1 < p < n )%Z /\ (prime p /\ Zdivide p n) ).
intros n Hn; generalize Hn; pattern n; apply Z_lt_induction; auto with zarith;
 clear n Hn.
intros n Rec H1 H2.
case (not_prime_divide _ H1 H2); intros m [Hm1 Hm2].
case (prime_dec m); intros Hm3.
exists m; auto.
case (Rec m); auto with zarith.
intros p [Hp [Hp1 Hp2]]; exists p; split; auto with zarith; split;
 auto with zarith.
apply Zdivide_trans with m; auto.
Qed.
 
Theorem prime_mod_3_4_divide_divide_first:
 forall p a b,
 prime p -> Zis_mod p 3 4 -> Zdivide p (a * a + b * b) ->  Zdivide p a.
intros p a b H1 H2 H3.
assert (Hp: 1 < p).
inversion H1; auto.
case (Z_eq_dec 0 (Zmod a p)); intros H4.
exists (Zdiv a p).
rewrite Zmult_comm; apply Z_div_exact_2; auto with zarith.
case (two_squares_exists_mod p b a); auto with zarith.
contradict H4.
apply sym_equal; replace 0 with (Zmod 0 p); auto with zarith.
apply Zis_mod_def_inv; auto with zarith.
case (Zdivide_dec p a); intros Hd.
case Hd; intros q Hq; exists q; rewrite <- Hq; auto with zarith.
apply Zis_mod_cancel with a; auto with zarith.
apply rel_prime_sym; apply prime_rel_prime; auto with zarith.
rewrite Zmult_0_r; auto.
case H3; intros q Hq; exists q; rewrite <- Hq; auto with zarith.
intros i Hi.
case two_squares_mod_inv with ( 2 := Hi ); auto; intros He.
absurd (Zmod p 4 = Zmod 3 4); auto with zarith.
rewrite He; intros; discriminate.
apply Zis_mod_def_inv; auto with zarith.
absurd (Zmod 1 4 = Zmod 3 4); auto with zarith.
intros; discriminate.
apply Zis_mod_def_inv; auto with zarith.
apply Zis_mod_trans with ( 2 := H2 ); auto.
apply Zis_mod_sym; auto with zarith.
Qed.
 
Theorem prime_mod_3_4_divide_divide_square:
 forall p a b,
 prime p ->
 Zis_mod p 3 4 -> Zdivide p (a * a + b * b) ->  Zdivide (p * p) (a * a + b * b).
intros p a b H1 H2 H3.
assert (Hp: 1 < p).
inversion H1; auto.
assert (Ha: Zdivide p a).
apply prime_mod_3_4_divide_divide_first with ( b := b ); auto with zarith.
assert (Hb: Zdivide p b).
apply prime_mod_3_4_divide_divide_first with ( b := a ); auto with zarith.
replace (b * b + a * a) with (a * a + b * b); auto with zarith.
exists (Zdiv a p * Zdiv a p + Zdiv b p * Zdiv b p).
pattern a at 1 2; rewrite (Zdivide_Zdiv_eq p a); auto with zarith.
pattern b at 1 2; rewrite (Zdivide_Zdiv_eq p b); auto with zarith; ring.
Qed.
 
Theorem two_squares_sum:
 forall n,
 0 <= n ->
 (forall p, prime p -> Zis_mod p 3 4 ->  Zeven (Zdiv_exp p n)) ->
  sum_of_two_squares n.
intros n Hn; generalize Hn; pattern n; apply Z_lt_induction; auto with zarith;
 clear n Hn.
intros n Rec H1 H2.
case Zle_lt_or_eq with ( 1 := H1 ); clear H1; intros H1.
2:exists 0; exists 0; rewrite <- H1; ring.
case (Zle_lt_or_eq 1 n); auto with zarith; clear H1; intros H1.
2:exists 1; exists 0; rewrite <- H1; ring.
case (prime_dec n); intros H3.
generalize (prime_case_4 _ H3); intros [H4|[H4|H4]].
apply two_squares_exists; auto.
apply two_squares_exists; auto.
absurd (Zeven (Zdiv_exp n n)); auto.
rewrite Zdiv_exp_id; auto with zarith.
case not_prime_prime_divide with ( 2 := H3 ); auto.
intros p [Hp1 [Hp2 Hp3]].
assert (n = p * Zdiv n p).
apply Zdivide_Zdiv_eq; auto with zarith.
assert (Hpp: 1 < p * p).
apply Zlt_le_trans with (1 * p); auto with zarith.
generalize (prime_case_4 _ Hp2); intros [H4|[H4|H4]].
subst p; rewrite H; apply two_squares_comp; auto with zarith.
apply two_squares_exists; auto with zarith.
apply Rec; auto with zarith.
intros p1 Hm1 Hm2.
rewrite <- Zdiv_exp_prime with ( c := 2 ); auto with zarith.
rewrite Zmult_comm; rewrite <- H; auto with zarith.
intros Hm3; absurd (Zmod p1 4 = Zmod 3 4); auto with zarith.
rewrite (prime_divide_prime_eq p1 2); auto with zarith.
intros; discriminate.
apply Zis_mod_def_inv; auto with zarith.
rewrite H; apply two_squares_comp; auto with zarith.
apply two_squares_exists; auto with zarith.
apply Rec; auto with zarith.
case (Zdivide_Zdiv_lt_pos p n); auto with zarith.
case (Zdivide_Zdiv_lt_pos p n); auto with zarith.
intros p1 Hm1 Hm2.
rewrite <- Zdiv_exp_prime with ( c := p ); auto with zarith.
rewrite Zmult_comm; rewrite <- H; auto with zarith.
apply Zmult_lt_reg_r with p; auto with zarith.
rewrite (Zmult_comm (Zdiv n p)); rewrite <- H; auto with zarith.
intros Hm3; absurd (Zmod 1 4 = Zmod 3 4); auto with zarith.
intros; discriminate.
apply trans_equal with (Zmod p1 4).
rewrite (prime_divide_prime_eq p1 p); auto with zarith.
apply sym_equal; apply Zis_mod_def_inv; auto with zarith.
apply Zis_mod_def_inv; auto with zarith.
assert (HH: Zdivide (p * p) n).
apply Zdivide_trans with (Zpower p (Zdiv_exp p n)); auto.
replace (p * p) with (Zpower p 2); auto with zarith.
exists (Zpower p (Zdiv_exp p n - 2)).
rewrite <- Zpower_exp; auto with zarith.
apply f_equal2 with ( f := Zpower ); auto with zarith.
case (Zle_lt_or_eq 0 (Zdiv_exp p n)); auto with zarith.
apply Zdiv_exp_pos; auto with zarith.
intros tmp; case (Zle_lt_or_eq 1 (Zdiv_exp p n)); auto with zarith.
intros tmp1; absurd (Zeven (Zdiv_exp p n)); auto with zarith.
rewrite <- tmp1; intros; intros tmp2; case tmp2.
intros tmp; case (Zdiv_exp_not_div p n); auto with zarith.
rewrite <- tmp; auto with zarith.
replace (p ^ (1 + 0)) with p; auto with zarith.
rewrite Zpower_exp_1; auto with zarith.
replace 2 with (1 + 1); auto with zarith.
(repeat (rewrite Zpower_exp || rewrite Zpower_exp_1)); auto with zarith.
apply Zdiv_exp_div; auto with arith.
case Hp1; auto.
apply Zle_trans with p; auto with zarith.
assert (H0: n = (p * p) * Zdiv n (p * p)).
pattern n at 1; rewrite (Z_div_mod_eq n (p * p)); auto with zarith.
rewrite (Zdivide_mod n (p * p)); auto with zarith.
case (Zle_lt_or_eq 1 (n / (p * p))).
case (Zdivide_Zdiv_lt_pos (p * p) n); auto with zarith.
intros Hk; rewrite H0; apply two_squares_comp; auto with zarith.
exists p; exists 0; ring.
apply Rec; auto with zarith.
case (Zdivide_Zdiv_lt_pos (p * p) n); auto with zarith.
intros p1 Hm1 Hm2.
case (Zdivide_dec p1 p); intros Hm3.
rewrite (prime_divide_prime_eq p1 p); auto with zarith.
replace (Zdiv_exp p (n / (p * p))) with (Zpred (Zpred (Zdiv_exp p n)));
 auto with zarith.
apply Zeven_pred; apply Zodd_pred; auto with zarith.
pattern n at 1; rewrite H0.
rewrite <- Zmult_assoc.
rewrite Zdiv_exp_succ; auto with zarith.
rewrite Zdiv_exp_succ; auto with zarith.
unfold Zpred; ring.
apply Zlt_le_trans with (p * 1); auto with zarith.
rewrite <- Zdiv_exp_prime with ( c := p ); auto with zarith.
rewrite <- Zdiv_exp_prime with ( c := p ); auto with zarith.
replace (((n / (p * p)) * p) * p) with n; auto with zarith.
apply trans_equal with ( 1 := H0 ); ring.
apply Zlt_le_trans with (1 * p); auto with zarith.
intros HH1; rewrite H0; rewrite <- HH1; exists p; exists 0; ring.
Qed.
 
Theorem two_squares_sum_converse:
 forall n,
 0 < n ->
 sum_of_two_squares n ->
 forall p, prime p -> Zis_mod p 3 4 ->  Zeven (Zdiv_exp p n).
intros n Hn Hn1; assert (Hp: 0 <= n); auto with zarith.
generalize Hn Hn1; pattern n; apply Z_lt_induction; auto with zarith;
 clear n Hn Hn1 Hp.
intros n Rec H1 H2 p H3 H4.
case (Zdivide_dec p n); intros Hdec.
case H2; intros a [b Ha1]; rewrite (Zabs_square a) in Ha1;
 rewrite (Zabs_square b) in Ha1; subst n.
assert (Hp: 1 < p).
inversion H3; auto.
assert (Ha: Zdivide p (Zabs a)).
apply prime_mod_3_4_divide_divide_first with ( b := Zabs b ); auto with zarith.
assert (Hb: Zdivide p (Zabs b)).
apply prime_mod_3_4_divide_divide_first with ( b := Zabs a ); auto with zarith.
replace (Zabs b * Zabs b + Zabs a * Zabs a)
     with (Zabs a * Zabs a + Zabs b * Zabs b); auto with zarith.
assert (Ha1: 0 <= Zabs a / p).
apply Zge_le; apply (Z_div_ge0 (Zabs a) p); intros; (try apply Zle_ge);
 auto with zarith.
assert (Hb1: 0 <= Zabs b / p).
apply Zge_le; apply (Z_div_ge0 (Zabs b) p); intros; (try apply Zle_ge);
 auto with zarith.
assert (Hu: 0 < (Zabs a / p) * (Zabs a / p) + (Zabs b / p) * (Zabs b / p)).
case (Zle_lt_or_eq 0 (Zabs a)); auto with zarith; intros Hr1.
case (Zdivide_Zdiv_lt_pos p (Zabs a)); auto with zarith; intros Hr2 Hr3.
apply Zlt_le_trans with ((Zabs a / p) * (Zabs a / p) + 0 * (Zabs b / p));
 auto with zarith.
rewrite Zmult_0_l; rewrite Zplus_0_r; replace 0 with (0 * (Zabs a / p));
 auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
rewrite <- Hr1; rewrite Zmult_0_l; rewrite Zplus_0_l.
case (Zle_lt_or_eq 0 (Zabs b)); auto with zarith; intros Hs1.
case (Zdivide_Zdiv_lt_pos p (Zabs b)); auto with zarith; intros Hs2 Hs3.
replace 0 with (0 * (Zabs b / p)); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
contradict H1; rewrite <- Hs1; rewrite <- Hr1; auto with zarith.
replace (Zdiv_exp p (Zabs a * Zabs a + Zabs b * Zabs b))
     with
      (Zsucc
        (Zsucc
          (Zdiv_exp
            p
            (Zdiv (Zabs a) p * Zdiv (Zabs a) p +
             Zdiv (Zabs b) p * Zdiv (Zabs b) p)))).
apply Zeven_Sn; apply Zodd_Sn; apply Rec; auto with zarith.
split; auto with zarith.
case (Zle_lt_or_eq 0 (Zabs a)); auto with zarith; intros Hr1.
case (Zdivide_Zdiv_lt_pos p (Zabs a)); auto with zarith; intros Hr2 Hr3.
case (Zle_lt_or_eq 0 (Zabs b)); auto with zarith; intros Hs1.
case (Zdivide_Zdiv_lt_pos p (Zabs b)); auto with zarith; intros Hs2 Hs3.
apply Zplus_lt_compat.
apply Zlt_trans with (Zabs a * (Zabs a / p)); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
apply Zlt_trans with (Zabs b * (Zabs b / p)); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
rewrite <- Hs1; replace (Zdiv 0 p) with 0.
(repeat rewrite Zmult_0_r); (repeat rewrite Zplus_0_r).
apply Zlt_trans with (Zabs a * (Zabs a / p)); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
unfold Zdiv; simpl; auto.
rewrite <- Hr1; replace (Zdiv 0 p) with 0.
(repeat rewrite Zmult_0_r); (repeat rewrite Zplus_0_l).
case (Zle_lt_or_eq 0 (Zabs b)); auto with zarith; intros Hs1.
case (Zdivide_Zdiv_lt_pos p (Zabs b)); auto with zarith; intros Hs2 Hs3.
apply Zlt_trans with (Zabs b * (Zabs b / p)); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
apply Zmult_lt_compat_l; auto with zarith.
contradict H1; rewrite <- Hs1; rewrite <- Hr1; auto with zarith.
unfold Zdiv; simpl; auto.
exists (Zabs a / p); exists (Zabs b / p); auto.
replace (Zabs a * Zabs a + Zabs b * Zabs b)
     with
      (p * (p * ((Zabs a / p) * (Zabs a / p) + (Zabs b / p) * (Zabs b / p)))).
(repeat rewrite Zdiv_exp_succ); auto with zarith.
apply Zlt_le_trans with (p * 1); auto with zarith.
pattern (Zabs a) at 3 4; rewrite (Zdivide_Zdiv_eq p (Zabs a)); auto with zarith.
pattern (Zabs b) at 3 4; rewrite (Zdivide_Zdiv_eq p (Zabs b)); auto with zarith.
ring.
replace (Zdiv_exp p n) with 0; auto with zarith.
apply Zdiv_exp_inv; auto with zarith.
inversion H3; auto.
rewrite Zplus_0_r; rewrite Zpower_exp_1; auto with zarith.
Qed.
