(*
  Copyright 2024 ZhengPu Shi
  This file is part of FunMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Qc (canonical rational number).
  author    : ZhengPu Shi
  date      : 2022.07
*)


Require Export QExt.
Require Export Qcanon.
Open Scope Qc.


(* ######################################################################### *)
(** * Algebraic Structures *)

(** equality is equivalence relation: Equivalence eq *)
Hint Resolve eq_equivalence : Qc.

(** operations are well-defined. Eg: Proper (eq ==> eq ==> eq) Qcplus *)

Lemma Qcplus_wd : Proper (eq ==> eq ==> eq) Qcplus.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcopp_wd : Proper (eq ==> eq) Qcopp.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcminus_wd : Proper (eq ==> eq ==> eq) Qcminus.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcmult_wd : Proper (eq ==> eq ==> eq) Qcmult.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcinv_wd : Proper (eq ==> eq) Qcinv.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcdiv_wd : Proper (eq ==> eq ==> eq) Qcdiv.
Proof. repeat (hnf; intros); subst; auto. Qed.

Hint Resolve
  Qcplus_wd Qcopp_wd Qcminus_wd
  Qcmult_wd Qcinv_wd Qcdiv_wd : Qc.

(** Associative *)

#[export] Instance Qcplus_Assoc : Associative Qcplus eq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcmult_Assoc : Associative Qcmult eq.
Proof. constructor; intros; field. Qed.

Hint Resolve Qcplus_Assoc Qcmult_Assoc : Qc.

(** Commutative *)

#[export] Instance Qcplus_Comm : Commutative Qcplus eq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcmult_Comm : Commutative Qcmult eq.
Proof. constructor; intros; field. Qed.

Hint Resolve Qcplus_Comm Qcmult_Comm : Qc.

(** Identity Left/Right *)
#[export] Instance Qcplus_IdL : IdentityLeft Qcplus 0 eq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcplus_IdR : IdentityRight Qcplus 0 eq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcmult_IdL : IdentityLeft Qcmult 1 eq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcmult_IdR : IdentityRight Qcmult 1 eq.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Qcplus_IdL Qcplus_IdR
  Qcmult_IdL Qcmult_IdR : Qc.

(** Inverse Left/Right *)

(** Distributive *)

#[export] Instance Qcmult_add_DistrL : DistrLeft Qcplus Qcmult eq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcmult_add_DistrR : DistrRight Qcplus Qcmult eq.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Qcmult_add_DistrL
  Qcmult_add_DistrR
  : Qc.

(** Semigroup *)

#[export] Instance Qcplus_SGroup : SGroup Qcplus eq.
Proof. constructor; auto with Qc. Qed.

#[export] Instance Qcmult_SGroup : SGroup Qcmult eq.
Proof. constructor; auto with Qc. Qed.

Hint Resolve
  Qcplus_SGroup
  Qcmult_SGroup
  : Qc.

(** Abelian semigroup *)

#[export] Instance Qcplus_ASGroup : ASGroup Qcplus eq.
Proof. constructor; auto with Qc. Qed.

#[export] Instance Qcmult_ASGroup : ASGroup Qcmult eq.
Proof. constructor; auto with Qc. Qed.

Hint Resolve
  Qcplus_ASGroup
  Qcmult_ASGroup
  : Qc.

(** Monoid *)
  
#[export] Instance Qcplus_Monoid : Monoid Qcplus 0 eq.
Proof. constructor; auto with Qc. Qed.

#[export] Instance Qcmult_Monoid : Monoid Qcmult 1 eq.
Proof. constructor; auto with Qc. Qed.

Hint Resolve
  Qcplus_Monoid
  Qcmult_Monoid
  : Qc.

(** Abelian monoid *)
  
#[export] Instance Qcplus_AMonoid : AMonoid Qcplus 0 eq.
Proof. constructor; auto with Qc. Qed.
  
#[export] Instance Qcmult_AMonoid : AMonoid Qcmult 1 eq.
Proof. constructor; auto with Qc. Qed.


(* ######################################################################### *)
(** ** Understanding the Qc type *)

(* Why Qc is better than Q *)
Section eq.
  (* Why 1#2 and 2#4 could be equal? *)
  
  (* Compute Q2Qc (1#2). *)
  (* = {| this := 1 # 2; canon := Qred_involutive (1 # 2) |} *)
  (* Compute Q2Qc (2#4). *)
  (* = {| this := 1 # 2; canon := Qred_involutive (2 # 4) |} *)

  (* Answer: because the Qc type.

     Record Qc : Set := Qcmake { 
       this : Q;  
       canon : Qred this = this }.

     Here, canon is a proof of equality, so its unique by the help of UIP.
     Then, only need the "this" component equal.
   *)
  Goal Q2Qc (1#2) = Q2Qc (2#4).
  Proof. cbv. f_equal. apply UIP. Qed.
End eq.


(* ######################################################################### *)
(** * Decidable *)

#[export] Instance Qc_eq_Dec : Dec (@eq Qc).
Proof. constructor. apply Qc_eq_dec. Defined.

#[export] Instance Qc_le_Dec : Dec Qcle.
Proof.
  constructor. intros. destruct (Qclt_le_dec b a); auto.
  right. intro. apply Qcle_not_lt in H. easy.
Defined.

#[export] Instance Qc_lt_Dec : Dec Qclt.
Proof.
  constructor. intros. destruct (Qclt_le_dec a b); auto.
  right. intro. apply Qcle_not_lt in q. easy.
Defined.

(* ~ (a < a) *)
Lemma Qc_lt_irrefl : forall a : Qc, ~ (a < a).
Proof.
  intros. intro. apply Qclt_not_eq in H. easy.
Qed.

(* a <> b -> a <= b -> a < b *)
Lemma Qcle_lt_strong : forall a b : Qc, a <> b -> a <= b -> a < b.
Proof.
  intros.
  destruct (Qc_dec a b) as [[H1|H1]|H1]; auto.
  - apply Qcle_not_lt in H0. easy.
  - subst. easy.
Qed.

(* c + a = c + b -> a = b *)
Lemma Qcplus_reg_l : forall a b c : Qc, c + a = c + b -> a = b.
Proof.
  intros.
  assert (-c + c + a = -c + c + b). { rewrite !associative. rewrite H. auto. }
  rewrite !inverseLeft in H0. rewrite !identityLeft in H0. auto.
Qed.

(* a + c = b + c -> a = b *)
Lemma Qcplus_reg_r : forall a b c : Qc, a + c = b + c -> a = b.
Proof.
  intros.
  assert (a + c + -c = b + c + -c). { rewrite H. auto. }
  rewrite !associative in H0. rewrite Qcplus_opp_r in H0.
  rewrite !Qcplus_0_r in H0. auto.
Qed.

(* a < b -> a + c < b + c *)
Lemma Qc_lt_add_compat_r : forall a b c : Qc, a < b -> a + c < b + c.
Proof.
  intros. pose proof (Qcplus_le_compat a b c c). destruct (Aeqdec a b).
  - subst. apply Qc_lt_irrefl in H. easy.
  - apply Qcle_lt_strong; auto.
    + intro. apply Qcplus_reg_r in H1. easy.
    + apply H0. apply Qclt_le_weak; auto. apply Qcle_refl.
Qed.

(* a < b -> c + a < c + b *)
Lemma Qc_lt_add_compat_l : forall a b c : Qc, a < b -> c + a < c + b.
Proof. intros. rewrite !(commutative c _). apply Qc_lt_add_compat_r; auto. Qed.

(* a < b -> 0 < c -> a * c < b * c *)
Lemma Qc_lt_mul_compat_r : forall a b c : Qc, a < b -> 0 < c -> a * c < b * c.
Proof. intros. apply Qcmult_lt_compat_r; auto. Qed.

(* a < b -> 0 < c -> c * a < c * b *)
Lemma Qc_lt_mul_compat_l : forall a b c : Qc, a < b -> 0 < c -> c * a < c * b.
Proof. intros. rewrite !(commutative c _). apply Qc_lt_mul_compat_r; auto. Qed.

(* n <= n *)
Lemma Qc_le_refl : forall n : Qc, n <= n.
Proof. apply Qcle_refl. Qed.


(** Bool version of "<" and "<=" for Qc *)
Definition Qcltb (a b : Qc) : bool := if Qclt_le_dec a b then true else false.
Definition Qcleb (a b : Qc) : bool := if Qclt_le_dec b a then false else true.
Infix "<?" := Qcltb : Qc_scope.
Infix "<=?" := Qcleb : Qc_scope.

Lemma Qcltb_reflect : forall a b : Qc, reflect (a < b) (a <? b).
Proof.
  intros. unfold Qcltb. destruct Qclt_le_dec; constructor; auto.
  apply Qcle_not_lt; auto.
Qed.

Lemma Qcleb_reflect : forall a b : Qc, reflect (a <= b) (a <=? b).
Proof.
  intros. unfold Qcleb. destruct Qclt_le_dec; constructor; auto.
  apply Qclt_not_le; auto.
Qed.

(* #[export] Instance Qc_Order : Order Qclt Qcle Qcltb Qcleb. *)
(* Proof. *)
(*   constructor; intros. *)
(*   - split; intros. apply Qcle_lt_or_eq; auto. destruct H. *)
(*     apply Qclt_le_weak; auto. subst. apply Qcle_refl. *)
(*   - apply Qc_lt_irrefl. *)
(*   - pose proof (Qclt_trans a b a H H0). apply Qc_lt_irrefl in H1. easy. *)
(*   - apply Qclt_trans with b; auto. *)
(*   - apply Qc_dec. *)
(*   - apply Qcltb_reflect. *)
(*   - apply Qcleb_reflect. *)
(* Qed. *)

Section test.
  Goal forall a b : Qc, {a = b} + {a <> b}.
  Proof. intros. apply Aeqdec. Abort.
End test.


(* ######################################################################### *)
(** ** Convertion between Qc and other types *)

(** Qc to Q *)
Definition Qc2Q (x : Qc) : Q := this x.

(** Z to Qc *)
Definition Z2Qc (x : Z) : Qc := Q2Qc (Z2Q x).

(** nat to Qc *)
Definition nat2Qc (x : nat) : Qc := Q2Qc (nat2Q x).

(** Qc to Z *)
Definition Qc2Z_ceiling (q : Qc) : Z := Q2Z_ceiling (Qc2Q q).
Definition Qc2Z_floor (q : Qc) : Z := Q2Z_floor (Qc2Q q).

(** list Q to list Qc *)
Definition Q2Qc_list l := map Q2Qc l.

(** dlist Q to dlist Qc *)
Definition Q2Qc_dlist dl := map Q2Qc_list dl.

(** list Qc to list Q, for better printing *)
Definition Qc2Q_list l := map Qc2Q l.

(** dlist Qc to dlist Q *)
Definition Qc2Q_dlist dl := map Qc2Q_list dl.

(** If two Q type value are equal, then its canonical form are equal *)
Lemma Qcmake_inversion : forall (q1 q2 : Q) (H1 : Qred q1 = q1) (H2 : Qred q2 = q2),
    q1 = q2 -> Qcmake q1 H1 = Qcmake q2 H2.
Proof.
  intros.
  f_equal.  (* Tips, f_equal has no effect on recrods of dependent types  *)
  subst. 
  f_equal. apply proof_irrelevance.
Qed.

(** Q2Qc (Qc2Q qc) = qc *)
Lemma Q2Qc_Qc2Q : forall (qc : Qc), Q2Qc (Qc2Q qc) = qc.
Proof.
  intros. unfold Qc2Q. unfold Q2Qc. destruct qc. simpl.
  f_equal.  (* Tips, f_equal has no effect on recrods of dependent types  *)
  apply Qcmake_inversion. auto.
Qed.

(** this (Q2Qc a) = Qred a *)
Lemma this_Q2Qc_eq_Qred : forall a : Q, this (Q2Qc a) = Qred a.
Proof. auto. Qed.


(* ######################################################################### *)
(** ** Properties for Qeqb and Qeq *)

Notation Qceqdec := Qc_eq_dec.

Notation Qceqb := Qc_eq_bool.

Infix     "=?"          := Qceqb          : Qc_scope.

(** Reflection of (=) and (=?) *)
Lemma Qceqb_true_iff : forall x y, x =? y = true <-> x = y.
Proof.
  intros; split; intros.
  - apply Qc_eq_bool_correct; auto.
  - subst. unfold Qceqb, Qc_eq_bool.
    unfold Qceqdec.
    destruct (Qeq_dec y y) eqn: E1; auto.
    destruct n. apply Qeq_refl.
Qed.

Lemma Qceqb_false_iff : forall x y, x =? y = false <-> x <> y.
Proof. 
  intros; split; intros.
  - intro. apply Qceqb_true_iff in H0. rewrite H in H0. easy.
  - destruct (Qceqb x y) eqn:E1; auto. apply Qceqb_true_iff in E1. easy.
Qed.


(* ######################################################################### *)
(** ** Others *)


(** ** sqrt of Q *)

(* Definition Qsqrt (q : Q) := Qmake (Z.sqrt (Qnum q)) (Pos.sqrt (Qden q)). *)

(* Example *)
(* Compute Qsqrt 1.21. *)