Require Export ZArith.
Require Export Znumtheory.
Require Export ZProd.
Require Export ZFact.
Require Import Permutation.
Require Import Iterator.
Require Import UList.
Open Scope Z_scope.
 
Definition Zis_mod := fun a b n => Zdivide n (a - b).
 
Theorem Zis_mod_def:
 forall a b n, 0 < n -> Zmod a n = Zmod b n ->  Zis_mod a b n.
intros a b n H H1; red.
exists (a / n - b / n).
apply trans_equal with ((n * (a / n) + b mod n) - (n * (b / n) + b mod n)).
pattern (b mod n) at 1; rewrite <- H1.
(repeat rewrite <- Z_div_mod_eq); auto with zarith.
ring.
Qed.
 
Theorem Zis_mod_def_inv:
 forall a b n, 0 < n -> Zis_mod a b n ->  Zmod a n = Zmod b n.
intros a b n H11 H2; replace a with ((a - b) + b); auto with zarith.
inversion_clear H2 as [x Hx].
rewrite Hx.
rewrite Zplus_comm; apply Z_mod_plus; auto with zarith.
Qed.
 
Theorem Zis_mod_ref: forall a n,  Zis_mod a a n.
intros a n; exists 0; auto with zarith.
Qed.
 
Theorem Zis_mod_mod: forall a n, 0 < n ->  Zis_mod a (Zmod a n) n.
intros a n H1; red.
pattern a at 1; rewrite (Z_div_mod_eq a n); auto with zarith.
exists (Zdiv a n); ring.
Qed.
 
Theorem Zis_mod_sym: forall a b n, Zis_mod a b n ->  Zis_mod b a n.
intros a b n H; red; replace (b - a) with (- (a - b)); auto with zarith.
Qed.
 
 
Theorem Zis_mod_trans:
 forall a b c n, Zis_mod a b n -> Zis_mod b c n ->  Zis_mod a c n.
intros a b c n H1 H2; red; replace (a - c) with ((a - b) + (b - c));
 auto with zarith.
Qed.

Theorem Zis_mod_plus:
 forall a b c d n, Zis_mod a b n -> Zis_mod c d n ->  Zis_mod (a + c) (b + d) n.
intros a b c d n [x H1] [y H2]; exists (x + y).
apply trans_equal with ((a - b) + (c - d)); auto with zarith.
rewrite H1; rewrite H2; auto with zarith.
Qed.
 
Theorem Zis_mod_minus:
 forall a b c d n, Zis_mod a b n -> Zis_mod c d n ->  Zis_mod (a - c) (b - d) n.
intros a b c d n [x H1] [y H2]; exists (x - y).
apply trans_equal with ((a - b) - (c - d)); auto with zarith.
rewrite H1; rewrite H2; ring.
Qed.
 
Theorem Zis_mod_minus_0: forall a b n, Zis_mod a b n ->  Zis_mod (a - b) 0 n.
intros a b n [x H1]; exists x; auto with zarith.
Qed.

Theorem Zis_mod_mult:
 forall a b c d n, Zis_mod a b n -> Zis_mod c d n ->  Zis_mod (a * c) (b * d) n.
intros a b c d n [x Hx] [y Hy].
exists (c * x + b * y).
apply trans_equal with (c * (a - b) + b * (c - d));
 [idtac | rewrite Hx; rewrite Hy]; ring.
Qed.
 
 
Theorem Zis_mod_cancel:
 forall a b c m, rel_prime a m -> Zis_mod (a * b) (a * c) m ->  Zis_mod b c m.
intros a b c m H1 H2.
assert (H3: Zdivide m (a * b - a * c)); auto with zarith.
assert (H4: Zdivide m (a * (b - c))); auto with zarith.
rewrite Zmult_minus_distr_l; auto with zarith.
red; apply Gauss with a; auto with zarith.
red.
red in H2 |-; auto with zarith.
Qed.
 
Theorem Zis_mod_square_1:
 forall p x,
 prime p -> Zis_mod (x * x) 1 p ->  Zis_mod x 1 p \/ Zis_mod x (p - 1) p.
intros p x H H1; red in H1 |-.
case (prime_mult p H (x + 1) (x - 1)); (try intros H2).
replace ((x + 1) * (x - 1)) with (x * x - 1); auto with zarith; ring.
right; red.
replace (x - (p - 1)) with ((x + 1) + - p); auto with zarith.
left; red; auto with zarith.
Qed.
 
 
 
