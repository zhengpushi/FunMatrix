(*
  Copyright 2024 ZhengPu Shi
  This file is part of FunMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : extension for Qc (canonical rational number).
  author    : ZhengPu Shi
  date      : 2022.07
*)


Require Export HierarchySetoid.
Require Export QExt.
Require Export Qcanon.
Open Scope Qc.


(* ######################################################################### *)
(** * Algebraic Structures *)

(** equality is equivalence relation: Equivalence eq *)
Hint Resolve eq_equivalence : Qc.

(** operations are well-defined. Eg: Proper (eq ==> eq ==> eq) Qcplus *)

Lemma Qcadd_wd : Proper (eq ==> eq ==> eq) Qcplus.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcopp_wd : Proper (eq ==> eq) Qcopp.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcsub_wd : Proper (eq ==> eq ==> eq) Qcminus.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcmul_wd : Proper (eq ==> eq ==> eq) Qcmult.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcinv_wd : Proper (eq ==> eq) Qcinv.
Proof. repeat (hnf; intros); subst; auto. Qed.

Lemma Qcdiv_wd : Proper (eq ==> eq ==> eq) Qcdiv.
Proof. repeat (hnf; intros); subst; auto. Qed.

Hint Resolve
  Qcadd_wd Qcopp_wd Qcsub_wd
  Qcmul_wd Qcinv_wd Qcdiv_wd : Qc.

(** Decidable *)

#[export] Instance Qc_eq_Dec : Dec (@eq Qc).
Proof. constructor. apply Qc_eq_dec. Defined.

#[export] Instance Qc_lt_Dec : Dec Qclt.
Proof.
  constructor. intros. destruct (Qclt_le_dec a b); auto.
  right. intro. apply Qcle_not_lt in q. easy.
Defined.

#[export] Instance Qc_le_Dec : Dec Qcle.
Proof.
  constructor. intros. destruct (Qclt_le_dec b a); auto.
  right. intro. apply Qcle_not_lt in H. easy.
Defined.

(** Associative *)

#[export] Instance Qcadd_Assoc : Associative eq Qcplus.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcmul_Assoc : Associative eq Qcmult.
Proof. constructor; intros; field. Qed.

Hint Resolve Qcadd_Assoc Qcmul_Assoc : Qc.

(** Commutative *)

#[export] Instance Qcadd_Comm : Commutative eq Qcplus.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcmul_Comm : Commutative eq Qcmult.
Proof. constructor; intros; field. Qed.

Hint Resolve Qcadd_Comm Qcmul_Comm : Qc.

(** Identity Left/Right *)

#[export] Instance Qcadd_IdL : IdentityLeft eq Qcplus 0.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcadd_IdR : IdentityRight eq Qcplus 0.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcmul_IdL : IdentityLeft eq Qcmult 1.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcmul_IdR : IdentityRight eq Qcmult 1.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Qcadd_IdL Qcadd_IdR
  Qcmul_IdL Qcmul_IdR : Qc.

(** Inverse Left/Right *)

#[export] Instance Qcadd_InvL : InverseLeft eq Qcplus 0 Qcopp.
Proof. constructor; intros; ring. Qed.

#[export] Instance Qcadd_InvR : InverseRight eq Qcplus 0 Qcopp.
Proof. constructor; intros; ring. Qed.

Hint Resolve Qcadd_InvL Qcadd_InvR : Qc.

(** Distributive *)

#[export] Instance Qcmul_add_DistrL : DistrLeft eq Qcplus Qcmult.
Proof. constructor; intros; field. Qed.

#[export] Instance Qcmul_add_DistrR : DistrRight eq Qcplus Qcmult.
Proof. constructor; intros; field. Qed.

Hint Resolve
  Qcmul_add_DistrL
  Qcmul_add_DistrR
  : Qc.

(** Semigroup *)

#[export] Instance Qcadd_SGroup : SGroup eq Qcplus.
Proof. constructor; auto with Qc. Qed.

#[export] Instance Qcmul_SGroup : SGroup eq Qcmult.
Proof. constructor; auto with Qc. Qed.

Hint Resolve
  Qcadd_SGroup
  Qcmul_SGroup
  : Qc.

(** Abelian semigroup *)

#[export] Instance Qcadd_ASGroup : ASGroup eq Qcplus.
Proof. constructor; auto with Qc. Qed.

#[export] Instance Qcmul_ASGroup : ASGroup eq Qcmult.
Proof. constructor; auto with Qc. Qed.

Hint Resolve
  Qcadd_ASGroup
  Qcmul_ASGroup
  : Qc.

(** Monoid *)
  
#[export] Instance Qcadd_Monoid : Monoid eq Qcplus 0.
Proof. constructor; auto with Qc. Qed.

#[export] Instance Qcmul_Monoid : Monoid eq Qcmult 1.
Proof. constructor; auto with Qc. Qed.

Hint Resolve
  Qcadd_Monoid
  Qcmul_Monoid
  : Qc.

(** Abelian monoid *)
  
#[export] Instance Qcadd_AMonoid : AMonoid eq Qcplus 0.
Proof. constructor; auto with Qc. Qed.
  
#[export] Instance Qcmul_AMonoid : AMonoid eq Qcmult 1.
Proof. constructor; auto with Qc. Qed.

Hint Resolve Qcadd_AMonoid Qcmul_AMonoid : Qc.

(** Group *)

#[export] Instance Qcadd_Group : Group eq Qcplus 0 Qcopp.
Proof. constructor; auto with Qc. Qed.

Hint Resolve Qcadd_Group : Qc.

(** AGroup *)

#[export] Instance Qcadd_AGroup : AGroup eq Qcplus 0 Qcopp.
Proof. constructor; auto with Qc. Qed.

Hint Resolve Qcadd_AGroup : Qc.

(** Ring *)

#[export] Instance Qc_Ring : Ring eq Qcplus 0 Qcopp Qcmult 1.
Proof. constructor; auto with Qc. Qed.

Hint Resolve Qc_Ring : Qc.

(** ARing *)

#[export] Instance Qc_ARing : ARing eq Qcplus 0 Qcopp Qcmult 1.
Proof. constructor; auto with Qc. Qed.

Hint Resolve Qc_ARing : Qc.

(** Field *)

#[export] Instance Qc_Field : Field eq Qcplus 0 Qcopp Qcmult 1 Qcinv.
Proof.
  constructor; auto with Qc.
  - intros. field; auto.
  - intro. easy.
Qed.

Hint Resolve Qc_Field : Qc.

(** Order *)

#[export] Instance Qc_Order : Order eq Qclt Qcle.
Proof.
  constructor; intros; try lia; auto with Qc; auto with qarith.
  - hnf; intros; hnf; intros. rewrite H,H0. easy.
  - intro. apply Qclt_not_eq in H. easy.
  - apply Qclt_trans with b; auto.
  - apply Qc_dec.
  - split; intros.
    apply Qcle_lt_or_eq; auto. destruct H.
    apply Qclt_le_weak; auto. subst. apply Qcle_refl.
Qed.


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
     Then, only need the "this" component equal. *)
  Goal Q2Qc (1#2) = Q2Qc (2#4).
  Proof. cbv. f_equal. apply UIP. Qed.
End eq.



(* (** Bool version of "<" and "<=" for Qc *) *)
(* Definition Qcltb (a b : Qc) : bool := if Qclt_le_dec a b then true else false. *)
(* Definition Qcleb (a b : Qc) : bool := if Qclt_le_dec b a then false else true. *)
(* Infix "<?" := Qcltb : Qc_scope. *)
(* Infix "<=?" := Qcleb : Qc_scope. *)

(* Lemma Qcltb_reflect : forall a b : Qc, reflect (a < b) (a <? b). *)
(* Proof. *)
(*   intros. unfold Qcltb. destruct Qclt_le_dec; constructor; auto. *)
(*   apply Qcle_not_lt; auto. *)
(* Qed. *)

(* Lemma Qcleb_reflect : forall a b : Qc, reflect (a <= b) (a <=? b). *)
(* Proof. *)
(*   intros. unfold Qcleb. destruct Qclt_le_dec; constructor; auto. *)
(*   apply Qclt_not_le; auto. *)
(* Qed. *)


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

(* Notation Qceqdec := Qc_eq_dec. *)

(* Notation Qceqb := Qc_eq_bool. *)

(* Infix     "=?"          := Qceqb          : Qc_scope. *)

(* (** Reflection of (=) and (=?) *) *)
(* Lemma Qceqb_true_iff : forall x y, x =? y = true <-> x = y. *)
(* Proof. *)
(*   intros; split; intros. *)
(*   - apply Qc_eq_bool_correct; auto. *)
(*   - subst. unfold Qceqb, Qc_eq_bool. *)
(*     unfold Qceqdec. *)
(*     destruct (Qeq_dec y y) eqn: E1; auto. *)
(*     destruct n. apply Qeq_refl. *)
(* Qed. *)

(* Lemma Qceqb_false_iff : forall x y, x =? y = false <-> x <> y. *)
(* Proof.  *)
(*   intros; split; intros. *)
(*   - intro. apply Qceqb_true_iff in H0. rewrite H in H0. easy. *)
(*   - destruct (Qceqb x y) eqn:E1; auto. apply Qceqb_true_iff in E1. easy. *)
(* Qed. *)


(* ######################################################################### *)
(** ** Others *)


(** ** sqrt of Q *)

(* Definition Qsqrt (q : Q) := Qmake (Z.sqrt (Qnum q)) (Pos.sqrt (Qden q)). *)

(* Example *)
(* Compute Qsqrt 1.21. *)
