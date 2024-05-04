(*
  Copyright 2024 ZhengPu Shi
  This file is part of FunMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Linear Space
  author    : ZhengPu Shi
  date      : 2024.01

  reference :
  1. 丘维声《高等代数》，第2版，清华大学出版社，2019
  2. Handbook of linear algebra, Leslie Hogben
Linear Algebra As an Introduction to Abstract Mathematics
  
  remark    :
  1. 向量空间推广到一般情形后称为线性空间，也简称为向量空间。
  2. ref : https://www.maths.tcd.ie/~dwilkins/Courses/111/vspace.pdf
 *)

Require Export HierarchySetoid.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A Aadd Azero Aopp Amul Aone Ainv Adiv Alt Ale
  V Vadd Vzero Vopp Vcmul
  W Wadd Wzero Wopp Wcmul.
Generalizable Variables B Badd Bzero.
Generalizable Variables C Cadd Czero.

Declare Scope LinearSpace_scope.
Delimit Scope LinearSpace_scope with LS.

Open Scope A_scope.
Open Scope LinearSpace_scope.

(* ===================================================================== *)
(** ** Linear Space *)

(* elements of V called vectors, and elements of K called scalars  *)
Class LinearSpace `{F : Field} {V : Type} (Veq : relation V) (Vadd : V -> V -> V)
  (Vzero : V) (Vopp : V -> V) (Vcmul : A -> V -> V) := {
    (* 8 axioms *)
    ls_vaddC :: Commutative Veq Vadd;
    ls_vaddA :: Associative Veq Vadd;
    ls_vaddIdR :: IdentityRight Veq Vadd Vzero;
    ls_vaddInvR :: InverseRight Veq Vadd Vzero Vopp;
    ls_vcmul_1_l : forall v : V, Veq (Vcmul Aone v) v;
    ls_vcmul_assoc : forall a b v,
      Veq (Vcmul (Amul a b) v) (Vcmul a (Vcmul b v));
    ls_vcmul_aadd : forall a b v,
      Veq (Vcmul (Aadd a b) v) (Vadd (Vcmul a v) (Vcmul b v));
    ls_vcmul_vadd : forall a u v,
      Veq (Vcmul a (Vadd u v)) (Vadd (Vcmul a u) (Vcmul a v));
    (* extra properites caused by Setoid equality "Veq" *)
    ls_aeq_equiv :: Equivalence Veq;
    ls_vadd_veq :: Proper (Veq ==> Veq ==> Veq) Vadd;
    ls_vopp_veq :: Proper (Veq ==> Veq) Vopp;
    ls_vcmul_veq :: Proper (Aeq ==> Veq ==> Veq) Vcmul
  }.

(** A field itself is a linear space *)
Section field_LinearSpace.
  Context `{HField : Field}.
  Add Field field_inst : (make_field_theory HField).
  
  #[export] Instance field_LinearSpace : LinearSpace Aeq Aadd Azero Aopp Amul.
  Proof. split; try apply HField. Qed.
End field_LinearSpace.

(** a real function is a linear space *)
(* ToDo *)

Section props.
  Context `{HLinearSpace : LinearSpace}.
  Add Field field_inst : (make_field_theory F).
  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "/ a" := (Ainv a) : A_scope.
  Notation Adiv := (fun a b => a * (/b)).
  Infix "/" := Adiv : A_scope.

  Infix "==" := Veq : LinearSpace_scope.
  Infix "+" := Vadd : LinearSpace_scope.
  Notation "0" := Vzero : LinearSpace_scope.
  Notation "- v" := (Vopp v) : LinearSpace_scope.
  Notation Vsub u v := (u + -v).
  Infix "-" := Vsub : LinearSpace_scope.
  Infix "\.*" := Vcmul : LinearSpace_scope.

  (** 0 + v == v *)
  #[export] Instance ls_vaddIdL : IdentityLeft Veq Vadd 0.
  Proof. constructor; intros. rewrite commutative, identityRight; easy. Qed.
  
  (** -v + v == 0 *)
  #[export] Instance ls_vaddInvL : InverseLeft Veq Vadd 0 Vopp.
  Proof. constructor; intros. rewrite commutative, inverseRight; easy. Qed.

  Hint Resolve ls_vaddIdL ls_vaddInvL : LS.
  
  (** 0 + v == v *)
  Lemma ls_vadd_0_l : forall v : V, 0 + v == v.
  Proof. intros. apply identityLeft. Qed.
  
  (** v + 0 == v *)
  Lemma ls_vadd_0_r : forall v : V, v + 0 == v.
  Proof. intros. apply identityRight. Qed.
  
  (** - v + v == 0 *)
  Lemma ls_vadd_vopp_l : forall v : V, - v + v == 0.
  Proof. intros. apply inverseLeft. Qed.
  
  (** v + - v == 0 *)
  Lemma ls_vadd_vopp_r : forall v : V, v + - v == 0.
  Proof. intros. apply inverseRight. Qed.
  
  (** <+,0,-v> forms an abelian-group *)
  #[export] Instance ls_vadd_AGroup : AGroup Veq Vadd 0 Vopp.
  Proof. repeat (constructor; try apply HLinearSpace; auto with LS). Qed.

  (** Cancellation law *)
  
  (** u + v == u + w -> v == w *)
  Theorem ls_cancel_l : forall u v w, u + v == u + w -> v == w.
  Proof. intros. apply group_cancel_l in H; auto. Qed.
  
  (** v + u == w + u -> v == w *)
  Theorem ls_cancel_r : forall u v w, v + u == w + u -> v == w.
  Proof. intros. apply group_cancel_r in H; auto. Qed.

  (** u + v == v -> u == 0 *)
  Theorem ls_add_eqR_imply0 : forall u v, u + v == v -> u == 0.
  Proof.
    intros. apply ls_cancel_r with (u:=v). rewrite H.
    pose proof ls_vadd_AGroup. agroup.
  Qed.
  
  (** u + v == u -> v == 0 *)
  Theorem ls_add_eqL_imply0 : forall u v, u + v == u -> v == 0.
  Proof.
    intros. apply ls_cancel_l with (u:=u). rewrite H.
    pose proof ls_vadd_AGroup. agroup.
  Qed.

  (** Vzero is unique *)
  Theorem ls_vzero_uniq_l : forall v0, (forall v, v0 + v == v) -> v0 == 0.
  Proof. intros. apply group_id_uniq_l; auto. Qed.
  
  Theorem ls_vzero_uniq_r : forall v0, (forall v, v + v0 == v) -> v0 == 0.
  Proof. intros. apply group_id_uniq_r; auto. Qed.

  (** (-v) is unique *)
  Theorem ls_vopp_uniq_l : forall v v', v + v' == 0 -> -v == v'.
  Proof. intros. eapply group_opp_uniq_l; auto. Qed.
  
  Theorem ls_vopp_uniq_r : forall v v', v' + v == 0 -> -v == v'.
  Proof. intros. eapply group_opp_uniq_r; auto. Qed.
  
  (** 0 .* v == 0 *)
  Theorem ls_vcmul_0_l : forall v : V, 0%A \.* v == 0.
  Proof.
    (* 0 .* v == (0 + 0) .* v == 0 .* v + 0 .* v, 0 .* v == 0 + 0 .* v,
       Hence, 0 .* v + 0 .* v == 0 + 0 .* v. By the cancellation law, then ... *)
    intros. pose proof ls_vadd_AGroup as HAGroup_vadd.
    assert (0%A \.* v + 0%A \.* v == 0%A \.* v + 0).
    - rewrite <- ls_vcmul_aadd. agroup. f_equiv. field.
    - apply ls_cancel_l in H. auto.
  Qed.

  (** a .* 0 == 0 *)
  Theorem ls_vcmul_0_r : forall a : A, a \.* 0 == 0.
  Proof.
    (* a*0 == a*0 + 0, a*0 == a*(0 + 0) == a*0 + a*0,
       Thus, a*0 + 0 == a*0 + a*0. By the cancellation law, then ... *)
    intros. pose proof ls_vadd_AGroup as HAGroup_vadd.
    assert (a \.* 0 == a \.* 0 + a \.* 0).
    { rewrite <- ls_vcmul_vadd. f_equal. agroup. }
    assert (a \.* 0 == a \.* 0 + 0). agroup.
    rewrite H in H0 at 1. apply ls_cancel_l in H0. auto.
  Qed.

  (** u + v == w -> u == w + - v *)
  Theorem ls_sol_l : forall u v w, u + v == w -> u == w + - v.
  Proof. intros. apply group_sol_l; auto. Qed.

  (** u + v == w -> v == - u + w *)
  Theorem ls_sol_r : forall u v w, u + v == w -> v == - u + w.
  Proof. intros. apply group_sol_r; auto. Qed.
  
  (** (- c) * v == - (c * v) *)
  Theorem ls_vcmul_opp : forall c v, (- c)%A \.* v == - (c \.* v).
  Proof.
    (* c*v + (-c)*v == 0, So, ... *)
    intros. symmetry. apply ls_vopp_uniq_l; auto.
    rewrite <- ls_vcmul_aadd. rewrite inverseRight, ls_vcmul_0_l; easy.
  Qed.
  
  (** c * (- v) == - (c * v) *)
  Theorem ls_vcmul_vopp : forall c v, c \.* (- v) == - (c \.* v).
  Proof.
    (* c*v + c*(-v) == 0, So, ... *)
    intros. symmetry. apply ls_vopp_uniq_l; auto.
    rewrite <- ls_vcmul_vadd. rewrite inverseRight, ls_vcmul_0_r; easy.
  Qed.
  
  (** (-1) * v == - v *)
  Theorem ls_vcmul_opp1 : forall v : V, (-(1))%A \.* v == -v.
  Proof. intros. rewrite ls_vcmul_opp, ls_vcmul_1_l; easy. Qed.

  (** v - v == 0 *)
  Theorem ls_vsub_self : forall v : V, v - v == 0.
  Proof. intros. pose proof ls_vadd_AGroup as HAGroup_vadd. agroup. Qed.

  Section AeqDec.
    Context {AeqDec : Dec Aeq}.
    
    (** a .* v == 0 -> a == 0 \/ v == 0 *)
    Theorem ls_vcmul_eq0_imply_k0_or_v0 : forall a v,
        a \.* v == 0 -> (a == 0)%A \/ v == 0.
    Proof.
      intros. destruct (dec a 0%A); auto. right.
      assert (/a \.* (a \.* v) == /a \.* 0) by (rewrite H; easy).
      rewrite <- ls_vcmul_assoc in H0.
      rewrite field_mulInvL in H0; auto.
      rewrite ls_vcmul_1_l, ls_vcmul_0_r in H0. auto.
    Qed.

    (** a <> 0 -> v <> 0 -> a .* v <> 0 *)
    Corollary ls_vcmul_neq0_if_neq0_neq0 : forall a v,
        ~(a == 0)%A -> ~(v == 0) -> ~(a \.* v == 0).
    Proof.
      intros. intro. apply ls_vcmul_eq0_imply_k0_or_v0 in H1. destruct H1; auto.
    Qed.
  End AeqDec.
  
End props.


(* ===================================================================== *)
(** ** Linear subspace (simply called subspace) from a linear space *)

(* A subset of vectors H ⊆ V from a linear space (V,F) forms a vector 
   subspace if the following three properties hold:
   1. The zero vector of V is in H
   2. H is closed under vector addition.
   3. H is closed under scalar multiplication. *)

(* The struct of a subspace. Here, H := {x | P x} *)
Class SubSpaceStruct `{HLinearSpace : LinearSpace} (P : V -> Prop) := {
    ss_zero_keep : P Vzero;
    ss_add_closed : forall {u v : sig P}, P (Vadd u.val v.val);
    ss_cmul_closed : forall {a : A} {v : sig P}, P (Vcmul a v.val);
    (* extra properites cause by Setoid equal "Veq" *)
    ss_P_veq :: Proper (Veq ==> iff) P
  }.

(* Is an element belong to H *)
Definition Hbelong `{ss: SubSpaceStruct} (v : V) : Prop := P v.

Section makeSubSpace.
  Context `{ss : SubSpaceStruct}.
  
  (** A subst of vectors H ⊆ V *)
  Notation H := (sig P).

  (** operations on H *)
  Definition Heq (u v : H) : Prop := Veq u.val v.val.
  Definition Hadd (u v : H) : H := exist _ (Vadd u.val v.val) ss_add_closed.
  Definition Hzero : H := exist _ Vzero ss_zero_keep.
  Definition Hopp (v : H) : H.
    refine (exist _ (Vopp v.val) _). rewrite <- ls_vcmul_opp1.
    apply ss_cmul_closed.
  Defined.
  Definition Hcmul (a : A) (v : H) : H := exist _ (Vcmul a v.val) ss_cmul_closed.

  (** Heq is Equivalence *)
  #[export] Instance Heq_Equiv : Equivalence Heq.
  Proof.
    constructor; hnf; intros; unfold Heq in *; try apply HLinearSpace.
    rewrite H; easy. rewrite H. easy.
  Qed.

  (** Hadd preserve Heq *)
  #[export] Instance Hadd_Heq : Proper (Heq ==> Heq ==> Heq) Hadd.
  Proof. simp_proper; intros; unfold Heq in *; simpl in *. rewrite H,H0. easy. Qed.

  (** Hopp preserve Heq *)
  #[export] Instance Hopp_Heq : Proper (Heq ==> Heq) Hopp.
  Proof. simp_proper; intros; unfold Heq in *; simpl in *. rewrite H. easy. Qed.

  (** Hcmul preserve Heq *)
  #[export] Instance Hcmul_Heq : Proper (Aeq ==> Heq ==> Heq) Hcmul.
  Proof. simp_proper; intros; unfold Heq in *; simpl in *. rewrite H,H0. easy. Qed.

  Lemma makeSubSpace : LinearSpace Heq Hadd Hzero Hopp Hcmul.
  Proof.
    repeat constructor; unfold Heq, Hadd, Hcmul; simpl; intros;
      try apply HLinearSpace; try apply Heq_Equiv.
    apply Hadd_Heq. apply Hopp_Heq. apply Hcmul_Heq.
  Qed.

End makeSubSpace.

(* we should make a subspace by a "ss : SubSpaceStruct" *)
Arguments makeSubSpace {A Aeq Aadd Azero Aopp Amul Aone Ainv F
                          V Veq Vadd Vzero Vopp Vcmul HLinearSpace P} ss.


(** 零子空间 *)
Section zero_SubSpace.
  Context `{HLinearSpace : LinearSpace}.
  
  Instance zero_SubSpaceStruct : SubSpaceStruct (fun v => Veq v Vzero).
  Proof.
    constructor; try easy.
    - intros. rewrite u.prf, v.prf. apply ls_vadd_0_l.
    - intros. rewrite v.prf. apply ls_vcmul_0_r.
    - simp_proper; intros. rewrite H. easy.
  Qed.

  #[export] Instance zero_SubSpace : LinearSpace Heq Hadd Hzero Hopp Hcmul :=
    makeSubSpace zero_SubSpaceStruct.
End zero_SubSpace.

(** 线性空间本身也是其子空间 *)
Section self_SubSpace.
  Context `{HLinearSpace : LinearSpace}.
  
  Instance self_SubSpaceStruct : SubSpaceStruct (fun v => True).
  Proof.
    constructor; auto.
    simp_proper; intros. easy.
  Qed.

  #[export] Instance self_SubSpace : LinearSpace Heq Hadd Hzero Hopp Hcmul :=
    makeSubSpace self_SubSpaceStruct.
  
End self_SubSpace.

