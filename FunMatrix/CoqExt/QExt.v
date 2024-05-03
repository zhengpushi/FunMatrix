(*
  Copyright 2024 ZhengPu Shi
  This file is part of FunMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Q (rational number).
  author    : ZhengPu Shi
  date      : 2022.04
*)


Require Export ZExt.
Require Export QArith Qround.
Open Scope Q.


(* ######################################################################### *)
(** * Algebraic Structures *)

(** equality is equivalence relation: Equivalence Qeq *)
Hint Resolve Q_Setoid : Q.

(** operations are well-defined. Eg: Proper (Qeq ==> Qeq ==> Qeq) Qplus *)
Hint Resolve
  Qplus_comp Qopp_comp Qminus_comp
  Qmult_comp Qinv_comp Qdiv_comp
  : Q.

(** Decidable *)

#[export] Instance Qeq_Dec : Dec Qeq.
Proof. constructor. intros. apply Qeq_dec. Defined.

#[export] Instance Qlt_Dec : Dec Qlt.
Proof.
  constructor. intros. destruct (Qlt_le_dec a b); auto.
  right. intro. apply Qle_not_lt in q. easy.
Defined.

#[export] Instance Qle_Dec : Dec Qle.
Proof.
  constructor. intros. destruct (Qlt_le_dec b a); auto.
  right. intro. apply Qle_not_lt in H. easy.
Defined.

(** Associative *)

#[export] Instance Qadd_Assoc : Associative Qplus Qeq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qmul_Assoc : Associative Qmult Qeq.
Proof. constructor; intros; field. Qed.

Hint Resolve Qadd_Assoc Qmul_Assoc : Q.

(** Commutative *)

#[export] Instance Qadd_Comm : Commutative Qplus Qeq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qmul_Comm : Commutative Qmult Qeq.
Proof. constructor; intros; field. Qed.

Hint Resolve Qadd_Comm Qmul_Comm : Q.

(** Identity Left/Right *)
#[export] Instance Qadd_IdL : IdentityLeft Qplus 0 Qeq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qadd_IdR : IdentityRight Qplus 0 Qeq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qmul_IdL : IdentityLeft Qmult 1 Qeq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qmul_IdR : IdentityRight Qmult 1 Qeq.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Qadd_IdL Qadd_IdR
  Qmul_IdL Qmul_IdR : Q.

(** Inverse Left/Right *)

#[export] Instance Qadd_InvL : InverseLeft Qplus 0 Qopp Qeq.
Proof. constructor; intros; ring. Qed.

#[export] Instance Qadd_InvR : InverseRight Qplus 0 Qopp Qeq.
Proof. constructor; intros; ring. Qed.

Hint Resolve Qadd_InvL Qadd_InvR : Q.

(** Distributive *)

#[export] Instance Qmul_add_DistrL : DistrLeft Qplus Qmult Qeq.
Proof. constructor; intros; field. Qed.

#[export] Instance Qmul_add_DistrR : DistrRight Qplus Qmult Qeq.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Qmul_add_DistrL
  Qmul_add_DistrR
  : Q.

(** Semigroup *)

#[export] Instance Qadd_SGroup : SGroup Qplus Qeq.
Proof. constructor; auto with Q. Qed.

#[export] Instance Qmul_SGroup : SGroup Qmult Qeq.
Proof. constructor; auto with Q. Qed.

Hint Resolve
  Qadd_SGroup
  Qmul_SGroup
  : Q.

(** Abelian semigroup *)

#[export] Instance Qadd_ASGroup : ASGroup Qplus Qeq.
Proof. constructor; auto with Q. Qed.

#[export] Instance Qmul_ASGroup : ASGroup Qmult Qeq.
Proof. constructor; auto with Q. Qed.

Hint Resolve
  Qadd_ASGroup
  Qmul_ASGroup
  : Q.

(** Monoid *)
  
#[export] Instance Qadd_Monoid : Monoid Qplus 0 Qeq.
Proof. constructor; auto with Q. Qed.

#[export] Instance Qmul_Monoid : Monoid Qmult 1 Qeq.
Proof. constructor; auto with Q. Qed.

Hint Resolve
  Qadd_Monoid
  Qmul_Monoid
  : Q.

(** Abelian monoid *)
  
#[export] Instance Qadd_AMonoid : AMonoid Qplus 0 Qeq.
Proof. constructor; auto with Q. Qed.
  
#[export] Instance Qmul_AMonoid : AMonoid Qmult 1 Qeq.
Proof. constructor; auto with Q. Qed.

Hint Resolve Qadd_AMonoid Qmul_AMonoid : Q.

(** Group *)

#[export] Instance Qadd_Group : Group Qplus 0 Qopp Qeq.
Proof. constructor; auto with Q. Qed.

Hint Resolve Qadd_Group : Q.

(** AGroup *)

#[export] Instance Qadd_AGroup : AGroup Qplus 0 Qopp Qeq.
Proof. constructor; auto with Q. Qed.

Hint Resolve Qadd_AGroup : Q.

(** Ring *)

#[export] Instance Q_Ring : Ring Qplus 0 Qopp Qmult 1 Qeq.
Proof. constructor; auto with Q. Qed.

Hint Resolve Q_Ring : Q.

(** ARing *)

#[export] Instance Q_ARing : ARing Qplus 0 Qopp Qmult 1 Qeq.
Proof. constructor; auto with Q. Qed.

Hint Resolve Q_ARing : Q.

(** Field *)

#[export] Instance Q_Field : Field Qplus 0 Qopp Qmult 1 Qinv Qeq.
Proof.
  constructor; auto with Q.
  - intros. field; auto.
  - intro. easy.
Qed.

Hint Resolve Q_Field : Q.

(** Order *)

#[export] Instance Q_Order : Order Qeq Qlt Qle.
Proof.
  constructor; intros; try lia; auto with Q; auto with qarith.
  - hnf; intros; hnf; intros. rewrite H,H0. easy.
  - apply Qlt_trans with b; auto.
  - apply Q_dec.
  - rewrite Qle_lteq. easy.
Qed.


(* ######################################################################### *)
(** * Convertion between Q and other types *)

(** Z to Q *)
Definition Z2Q (z : Z) : Q := inject_Z z.

(** nat to Q *)
Definition nat2Q (n : nat) : Q := Z2Q (Z.of_nat n).

(** Q to Z *)
Definition Q2Z_ceiling (q : Q) : Z := Qceiling q.
Definition Q2Z_floor (q : Q) : Z := Qfloor q.


(* ######################################################################### *)
(** * Properties for Qeqb and Qeq *)

(** This axiom just for convenient printing and parsing, LIMITED USE IT.
  
  For example, 3#2 and 6#4 is equivalent, but they are not the same.
  We mainly use this axiom to ensure 3#2 = 6#4, but not to say 3=6 and 2=4.
  
  Be careful for use of any axiom!!
*)
(* Axiom Qeq_iff_eq : forall (a b : Q), Qeq a b <-> a = b. *)

(* Lemma Qneq_iff_neq : forall (a b : Q), ~(Qeq a b) <-> a <> b. *)
(* Proof. *)
(*   intros. split; intros. *)
(*   - intro. apply Qeq_iff_eq in H0. easy. *)
(*   - intro. apply Qeq_iff_eq in H0. easy. *)
(* Qed. *)

(* Lemma Qeqdec : forall q1 q2 : Q, {q1 = q2} + {q1 <> q2}. *)
(* Proof. *)
(*   intros a b. *)
(*   destruct (Qeq_dec a b) as [H|H] eqn : E1. *)
(*   - left. apply Qeq_iff_eq. auto. *)
(*   - right. intro. apply Qeq_iff_eq in H0. auto. *)
(* Defined. *)

Definition Qeqb := Qeq_bool.

Infix     "=="          := Qeq            : Q_scope.
(* Notation  "a ~= b"      := (~(a == b))    : Q_scope. *)
Infix     "=?"          := Qeqb           : Q_scope.

(** Reflection of (==) and (=?) *)
Lemma Qeqb_true_iff_equiv : forall x y, x =? y = true <-> x == y.
Proof.
  apply Qeq_bool_iff.
Qed.

Lemma Qeqb_false_iff_equiv : forall x y, x =? y = false <-> ~ x == y.
Proof. 
  intros; split; intros.
  - intro. apply Qeqb_true_iff_equiv in H0. rewrite H in H0. easy.
  - destruct (Qeqb x y) eqn:E1; auto. apply Qeqb_true_iff_equiv in E1. easy.
Qed.

(* Lemma Qeqb_true_iff : forall x y, x =? y = true <-> x = y. *)
(* Proof. *)
(*   intros; split; intros. *)
(*   - apply Qeq_iff_eq. apply Qeqb_true_iff_equiv. auto. *)
(*   - apply Qeq_iff_eq in H. apply Qeqb_true_iff_equiv. auto. *)
(* Qed. *)

(* Lemma Qeqb_false_iff : forall x y, x =? y = false <-> x <> y. *)
(* Proof.  *)
(*   intros; split; intros. *)
(*   - intro. apply Qeq_iff_eq in H0. apply Qeqb_false_iff_equiv in H. easy. *)
(*   - apply Qeqb_false_iff_equiv. apply Qneq_iff_neq. auto. *)
(* Qed. *)

(* (** (==) is equivalence relation *) *)
(* Lemma Qeq_equiv : equivalence _ Qeq. *)
(* Proof. *)
(*   split;intro;intros;try easy. rewrite H;try easy. *)
(* Qed. *)


(* ######################################################################### *)
(** * Others *)

(** This is needed by field_theory (EQ version, original is equiv version) *)
(* Lemma Qmul_inv_l_EQ : forall p : Q, p <> 0 -> /p * p = 1. *)
(* Proof. *)
(*   intros. apply Qeq_iff_eq. rewrite Qmul_comm. *)
(*   apply Qmul_inv_r. apply Qneq_iff_neq. auto. *)
(* Qed. *)
 

(** ** sqrt of Q *)

(** A very rough algorithm for square root of rational number *)
Definition Qsqrt (q : Q) := Qmake (Z.sqrt (Qnum q)) (Pos.sqrt (Qden q)).

(* Example *)
(* Compute Qsqrt 1.21. *)

