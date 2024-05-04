(*
  Copyright 2024 ZhengPu Shi
  This file is part of FunMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension for list (Setoid version)
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. reference "A Gentle Introduction to Type Classes and Relations in Coq"
  2. main contribution
     list
        operations and propertities of list
     dlist
        operations and propertities of list
  3. eq and Aeq
  (1) Aeq is setoid version, and eq is a special case of Aeq.
      i.e., if we can prove a proposition over "Aeq", then "eq" is automatically satisfy.
      But, a different case is "eqlistA eq", that is not exactly same as "@eq (list A)"
  (2) The "Aeq" is designed for better polymorphism.
  
  history   :
  1. 2021.12, by ZhengPu Shi.
     first version

  2. 2022.05, by ZhengPu Shi.
     split big file into small modules

  3. 2022.10, by ZhengPu Shi
     Setoid version

  4. 2023.11, by ZhengPu Shi
     Leibniz Equality version

  5. 2024.04, by ZhengPu Shi
     Setoid version
 *)

Require Export HierarchySetoid.
Require Import StrExt NatExt.
Require Export List SetoidList. Export ListNotations.

Open Scope A_scope.
Open Scope list_scope.

Generalizable Variables A Aeq Aadd Azero Aopp Amul Aone Ainv Alt Ale.
Generalizable Variables B Beq.
Generalizable Variables C Ceq.

Notation dlist A := (list (list A)).

Hint Resolve
  repeat_length seq_length map_length
  : list.


(* ##################################################################### *)
(** * list *)

(* ======================================================================= *)
(** ** eqlistA is Dec *)

(** (eqlistA Aeq) is Dec *)
#[export] Instance eqlistA_Dec : forall `{Dec A Aeq}, Dec (eqlistA Aeq).
Proof.
  intros. constructor; intros l1 l2. revert l2.
  induction l1,l2; intros; simpl in *.
  - left. easy.
  - right. intro H1; inv H1.
  - right. intro H1; inv H1.
  - destruct (dec a a0).
    + destruct (IHl1 l2). left. auto. right. intro. inv H0. easy.
    + right. intro. inv H0. easy.
Defined.


(* ======================================================================= *)
(** ** Equalities on list A *)

(** `eqlistA eq` equal to `eq` *)
Lemma eqlistA_eq_is_eq : forall {A} (l1 l2 : list A),
    eqlistA eq l1 l2 <-> l1 = l2.
Proof.
  intros A l1. induction l1, l2; simpl; split; intros; auto; try easy.
  - inv H. f_equal. apply IHl1. auto.
  - inv H. easy.
Qed.

(** `eqlistA eqlistA eq` equal to `eq` *)
Lemma eqlistA_eqlistA_eq_is_eq : forall {A} (l1 l2 : dlist A),
    eqlistA (eqlistA eq) l1 l2 <-> l1 = l2.
Proof.
  intros A l1. induction l1; destruct l2; simpl; split; intros; auto; try easy.
  - inv H. f_equal.
    + apply eqlistA_eq_is_eq; auto.
    + apply IHl1. auto.
  - inv H. easy.
Qed.

Section dec.
  Context `{Aequiv : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Context `{AeqDec : Dec _ Aeq}.

  (** list equality is decidable on setoid *)
  Lemma list_eq_dec : forall l1 l2 : list A, {l1 == l2} + {~(l1 == l2)}.
  Proof.
    intros l1. induction l1, l2; intros; try (left; easy); try (right; easy).
    destruct (dec a a0),(IHl1 l2); auto.
    - right. intro. inv H; easy.
    - right. intro. inv H; easy.
    - right. intro. inv H; easy.
  Qed.
End dec.


(* ===================================================================== *)
(** ** Properties of cons *)
Section cons.

  Context `{Aeq : relation A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.

  (** cons is a proper morphism *)
  #[export] Instance cons_wd : Proper (Aeq ==> eqlistA Aeq ==> eqlistA Aeq) (@cons A).
  Proof. simp_proper; intros. destruct x0,y0; auto. Qed.

  (** Equality of cons, iff both parts are equal *)
  Lemma cons_eq_iff : forall (a1 a2 : A) (l1 l2 : list A),
      a1 :: l1 == a2 :: l2 <-> (a1 == a2)%A /\ l1 == l2.
  Proof. intros. split; intros H; inversion H; auto. Qed.

  (** Inequality of cons, iff at least one parts are not equal *)
  Lemma cons_neq_iff : forall (a1 a2 : A) (l1 l2 : list A),
      ~(a1 :: l1 == a2 :: l2) <-> (~(a1 == a2)%A \/ ~(l1 == l2)).
  Proof. intros. rewrite cons_eq_iff. tauto. Qed.

End cons.


(* ===================================================================== *)
(** ** Properties of length *)
Section length.
  Context `{Aequiv : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  
  (** length of a list is zero, iff the list is nil *)
  (* Note, make it as transparent, it is useful for expression evaluation *)
  Lemma length_zero_iff_nil : forall (l : list A), length l = 0 <-> l == [].
  Proof. intros. destruct l; intros; split; intros; auto; try easy. Defined.

  (** decompose a list which length is 1 *)
  Lemma list_length1 : forall (l : list A),
      length l = 1 -> {x | l == [x]}.
  Proof. 
    destruct l; intros. inversion H. inversion H.
    apply length_zero_iff_nil in H1. exists a. rewrite H1. easy.
  Defined.

  (** a list has only one element equal to [hd _ l] *)
  Lemma list_length1_eq_hd : forall (x : A) (l : list A), 
      length l = 1 -> l == [hd x l].
  Proof.
    intros x l. destruct l; intros; simpl in *. lia.
    f_equiv. apply length_zero_iff_nil. lia.
  Qed.

  (** decompose a list which length is S n *)
  Lemma list_length_Sn : forall (l : list A) n,
      length l = S n -> {x & { t | l == x :: t}}.
  Proof. destruct l; intros. inversion H. exists a. exists l. easy. Qed.

  (** decompose a list which length is S (S n) *)
  Lemma list_length_SSn : forall (l : list A) n,
      length l = S (S n) -> {x & { y & { t | l == x :: y :: t}}}.
  Proof.
    intros. destruct l; intros. inversion H.
    exists a. destruct l. inversion H. exists a0. exists l. easy.
  Qed.

End length.

Section Test.
  Context {A} (a : A).
  Let l := [a].
  
  (* The proof of `length l = 1` should be end by `Defined` *)
  Let H : length l = 1. auto. Defined.
  (* Compute proj1_sig (list_length1 l H). *)
  
End Test.


(* ===================================================================== *)
(** ** Customized list induction *)
Section ind.

  Context {A : Type}.

  (** Connect induction principle between nat and list *)
  (* Lemma ind_nat_list : forall (P : list A -> Prop) , *)
  (*     (forall n l, length l = n -> P l) -> (forall l, P l). *)
  (* Proof. *)
  (*   intros. apply (H (length l)). auto. *)
  (* Qed. *)

  (** Two step induction principle for list *)
  Theorem list_ind2 : forall (P : list A -> Prop),
      (P []) -> 
      (forall a, P [a]) -> 
      (forall l a b, P l -> P (a :: b :: l)) ->
      (forall l, P l).
  Proof.
    intros P H0 H1 H2. apply ind_nat_list. induction n using nat_ind2. 
    - intros. apply List.length_zero_iff_nil in H; subst; auto.
    - intros. repeat (destruct l; simpl in *; try lia). auto.
    - destruct l; auto. destruct l; auto.
      intros. apply H2. apply IHn. simpl in H. lia.
  Qed.
End ind.

(* ===================================================================== *)
(** ** about "repeat" *)
Section repeat.
  Context `{Aequiv : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.

  #[export] Instance repeat_wd : Proper (Aeq ==> eq ==> eqlistA Aeq) (@repeat A).
  Proof.
    simp_proper. intros. subst. rename y0 into n.
    induction n; simpl; try easy. f_equiv; auto.
  Qed.
    
  (** repeat S n times equal to another form *)
  Lemma repeat_Sn (Azero : A) : forall n, repeat Azero (S n) = Azero :: repeat Azero n.
  Proof. intros. simpl. auto. Qed.

End repeat.

(* ===================================================================== *)
(** ** Properties of hd and tl *)
Section hd_tl.
  Context {A : Type}.

  (** length of tl. (pred version) *)
  Lemma tl_length : forall (l : list A), length (tl l) = pred (length l).
  Proof. induction l; auto. Qed.
  
  Context `{Aequiv : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.

  (** hd is a proper morphism *)
  #[export] Instance hd_wd : Proper (Aeq ==> eqlistA Aeq ==> Aeq) (@hd A).
  Proof. simp_proper; intros. destruct x0,y0; simpl; try easy. inv H0; auto. Qed.
  
  (** tl is a proper morphism *)
  #[export] Instance tl_wd : Proper (eqlistA Aeq ==> eqlistA Aeq) (@tl A).
  Proof. simp_proper; intros. destruct x,y; simpl; try easy. inv H; auto. Qed.
  
  Context {Azero : A}.
  
  (** hd of a list equal to 0-th element *)
  Lemma hd_eq_nth_0 : forall (l : list A), (hd Azero l == nth 0 l Azero)%A.
  Proof. intros. destruct l; simpl; reflexivity. Qed.

End hd_tl.


(* ===================================================================== *)
(** ** Properties of nth *)
Section nth.
  
  Context `{Equiv_Aeq : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  
  (** nth is a proper morphism *)
  #[export] Instance nth_wd : Proper (eq ==> eqlistA Aeq ==> Aeq ==> Aeq) (@nth A).
  Proof.
    simp_proper. intros i j H. inv H. rename j into i. intros l1 l2. revert l2 i.
    induction l1; destruct l2,i; intros; simpl in *; try easy.
    inv H. easy. inv H. auto.
  Qed.
  
  (** nth [] a = a *)
  Lemma nth_nil : forall (a : A) (i : nat), (nth i [] a == a)%A.
  Proof. intros. destruct i; simpl; easy. Qed.

  Context (Azero : A).

  (** Two list equal iff all nth visit equal *)
  Lemma list_eq_iff_nth :
    forall n (l1 l2 : list A) (H1 : length l1 = n) (H2 : length l2 = n),
      l1 == l2 <-> (forall (i : nat), i < n -> (nth i l1 Azero == nth i l2 Azero)%A).
  Proof.
    intros. split; intros.
    - rewrite H. reflexivity.
    - generalize dependent l2. generalize dependent n.
      induction l1; intros; simpl in *; subst.
      + symmetry. apply length_zero_iff_nil; auto.
      + destruct l2; simpl in *; try easy. f_equiv.
        * specialize (H 0); simpl in H. apply H. lia.
        * apply (IHl1 (length l2)); auto; try lia. intros. apply (H (S i)). lia.
  Qed.

  (** Get from `repeat x` with `x` always return x *)
  Lemma nth_repeat_same : forall (n i : nat) (x : A),
      (nth i (repeat x n) x == x)%A.
  Proof. induction n, i; intros; simpl; try easy. Qed.

  (** Get from `repeat x` with in-range-index always return x *)
  Lemma nth_repeat_inRange : forall (n i : nat) (x y : A),
      i < n -> (nth i (repeat x n) y == x)%A.
  Proof. induction n, i; intros; simpl; try easy. apply IHn. lia. Qed.

End nth.

(* ===================================================================== *)
(** ** Split a list with given length using `nth` *)

Section list2elems.
  Context {A} {Azero : A}.
  Notation "l ! i" := (nth i l Azero) (at level 2).

  (** a list of length 1 *)
  Lemma list2elems_1 : forall (l : list A), length l = 1 -> l = [l!0].
  Proof. intros. repeat (destruct l; simpl in *; try lia); auto. Qed.

  (** a list of length 2 *)
  Lemma list2elems_2 : forall (l : list A), length l = 2 -> l = [l!0; l!1].
  Proof. intros. repeat (destruct l; simpl in *; try lia); auto. Qed.

  (** a list of length 3 *)
  Lemma list2elems_3 : forall (l : list A), length l = 3 -> l = [l!0; l!1; l!2].
  Proof. intros. repeat (destruct l; simpl in *; try lia); auto. Qed.

  (** a list of length 4 *)
  Lemma list2elems_4 : forall (l : list A), length l = 4 -> l = [l!0; l!1; l!2; l!3].
  Proof. intros. repeat (destruct l; simpl in *; try lia); auto. Qed.

End list2elems.


(* ===================================================================== *)
(** ** nthFull : nth element with index-in-the-bound *)
Section nthFull.
  Context {A : Type}.

  (* Get element of a list.
     This is very similiar with `nth`, but needn't a default value *)
  Definition nthFull (l : list A) (i : nat) (H : i < length l) : A.
  Proof.
    destruct l.
    - simpl in H. apply Nat.nlt_0_r in H. contradiction.
    - exact (nth i (a :: l) a).
  Defined.

  Context `{Aequiv : Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  
  Lemma nthFull_eq_nth : forall (Azero : A) (l : list A) (i : nat) (H : i < length l),
      (nthFull l i H == nth i l Azero)%A.
  Proof.
    destruct l,i; intros; simpl in *; try easy.
    rewrite nth_indep with (d':=Azero); try easy. lia.
  Qed.
  
End nthFull.


(* ===================================================================== *)
(** ** Properties of fold_left *)
Section fold_left.

  Context `{M : Monoid}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.

  (** fold_left is a proper relation *)
  #[export] Instance fold_left_wd :
    Proper (eqlistA Aeq ==> Aeq ==> Aeq) (fold_left Aadd).
  Proof.
    intros l1. induction l1; intros l2 Hl a1 a2 Ha.
    - inv Hl. simpl. auto.
    - destruct l2. easy. inv Hl. simpl. apply IHl1; auto. rewrite Ha,H2. easy.
  Qed.
  
  Context `{HAMonoid:AMonoid A Aeq Aadd 0}.
  
  Lemma fold_left_rebase_l : forall (l : list A) a b,
      (fold_left Aadd l (a + b) == (fold_left Aadd l a) + b)%A.
  Proof.
    induction l; intros; simpl; try easy.
    assert (a0 + b + a == a0 + a + b)%A. amonoid.
    rewrite H. rewrite IHl. easy.
  Qed.

  Lemma fold_left_rebase_r : forall (l : list A) a b,
      (fold_left Aadd l (a + b) == (fold_left Aadd l b) + a)%A.
  Proof.
    intros. rewrite (commutative a b). rewrite fold_left_rebase_l. easy.
  Qed.

  (** (a+0+0+0+... = a *)
  Lemma fold_left_lzero : forall n a, (fold_left Aadd (repeat 0 n) a == a)%A.
  Proof.
    induction n; intros; simpl; try easy.
    rewrite fold_left_rebase_r. rewrite IHn. amonoid.
  Qed.

  (** Σ(ai+bi) = Σ(ai) + Σ(bi) *)
  Lemma fold_left_add : forall (l l1 l2 : list A) n,
      length l = n -> length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l 0 == nth i l1 0 + nth i l2 0)%A ->
      (fold_left Aadd l 0 == (fold_left Aadd l1 0) + (fold_left Aadd l2 0))%A.
  Proof.
    induction l; destruct l1,l2; intros; simpl in *; try lia. amonoid.
    destruct n. lia.
    inv H1. inv H0. inv H. 
    (* inversion H; clear H. inversion H0; clear H0. inversion H1; clear H1. *)
    rewrite !fold_left_rebase_l.
    rewrite (IHl l1 l2 (length l)); auto; try lia.
    - amonoid. specialize (H2 O); simpl in H2. apply H2. lia.
    - intros. specialize (H2 (S i)); simpl in H2. apply H2. lia.
  Qed.

  Context `{HGroup:Group A Aeq Aadd 0 Aopp}.
  
  (** (-a1)+(-a2)+... == -(a1+a2+...) *)
  Lemma fold_left_opp : forall (l1 l2 : list A) n,
      length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l1 0 == Aopp (nth i l2 0))%A ->
      (fold_left Aadd l1 0 == Aopp (fold_left Aadd l2 0))%A.
  Proof.
    induction l1,l2; intros; simpl in *; try lia. group.
    destruct n. lia.
    inversion H; clear H. inversion H0; clear H0.
    rewrite !fold_left_rebase_l.
    rewrite (IHl1 l2 n); auto.
    - agroup. specialize (H1 O); simpl in H1. rewrite H1; try easy; try lia.
    - intros. specialize (H1 (S i)). simpl in H1. apply H1. lia.
  Qed.

  Context `{HARing : ARing A Aeq Aadd 0 Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Infix "*" := Amul : A_scope.

  (** k*a1+k*a2+... == k * (a1+a2+...) *)
  Lemma fold_left_cmul : forall (l1 l2 : list A) n a,
      length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l1 0 == a * (nth i l2 0))%A ->
      (fold_left Aadd l1 0 == a * (fold_left Aadd l2 0))%A.
  Proof.
    induction l1,l2; intros; simpl in *; try lia. ring.
    destruct n; try lia.
    inversion H; clear H. inversion H0; clear H0.
    rewrite !fold_left_rebase_l.
    rewrite (IHl1 l2 n a1); auto.
    - ring_simplify. agroup.
      specialize (H1 O); simpl in H1. rewrite H1; try easy; try lia.
    - intros. specialize (H1 (S i)); simpl in H1. apply H1. lia.
  Qed.

End fold_left.


(* ===================================================================== *)
(** ** Properties of fold_right *)
Section fold_right.

  Context `{M : Monoid}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.

  (** fold_right is a proper relation *)
  #[export] Instance fold_right_wd :
    Proper (Aeq ==> eqlistA Aeq ==> Aeq) (fold_right Aadd).
  Proof.
    intros x y Hxy l1 l2. revert l2 x y Hxy.
    induction l1,l2; intros; simpl in *; auto; try easy. inv H.
    rewrite H3. rewrite (IHl1 l2 x y); auto. easy.
  Qed.
  
  Context `{HAMonoid:AMonoid A Aeq Aadd 0}.
  
  Lemma fold_right_rebase_l : forall (l : list A) a b,
      (fold_right Aadd (a + b) l == b + (fold_right Aadd a l))%A.
  Proof.
    induction l; intros; simpl; auto. agroup. rewrite IHl. agroup.
  Qed.

  Lemma fold_right_rebase_r : forall (l : list A) a b,
      (fold_right Aadd (a + b) l == a + (fold_right Aadd b l))%A.
  Proof.
    induction l; intros; simpl; auto. easy. rewrite IHl. group.
  Qed.

  (** (a+0+0+0+... == a *)
  Lemma fold_right_lzero : forall n a,
      (fold_right Aadd a (repeat 0 n) == a)%A.
  Proof. induction n; intros; simpl; try easy. rewrite IHn. agroup. Qed.
  
  (** Σ(ai+bi) = Σ(ai) + Σ(bi) *)
  Lemma fold_right_add : forall (l l1 l2 : list A) n,
      length l = n -> length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l 0 == nth i l1 0 + nth i l2 0)%A ->
      (fold_right Aadd 0 l == (fold_right Aadd 0 l1) + (fold_right Aadd 0 l2))%A.
  Proof.
    induction l; destruct l1,l2; intros; simpl in *; try lia. agroup.
    destruct n; try lia. rewrite (IHl l1 l2 n); auto.
    - specialize (H2 O); simpl in H2. rewrite H2; try lia. agroup.
    - intros. specialize (H2 (S i)); simpl in H2. rewrite H2; try easy. lia.
  Qed.

  Context `{HGroup:Group A Aeq Aadd 0 Aopp}.

  (** (-a1)+(-a2)+... = -(a1+a2+...) *)
  Lemma fold_right_opp : forall (l1 l2 : list A) n,
      length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l1 0 == Aopp (nth i l2 0))%A ->
      (fold_right Aadd 0 l1 == Aopp (fold_right Aadd 0 l2))%A.
  Proof.
    induction l1,l2; intros; simpl in *; try lia. group.
    destruct n; try lia. rewrite (IHl1 l2 n); auto.
    - specialize (H1 O); simpl in H1.
      rewrite H1; try lia. rewrite group_opp_distr. agroup.
    - intros. specialize (H1 (S i)); simpl in H1. rewrite H1; try easy. lia.
  Qed.

  Context `{HARing:ARing A Aeq Aadd 0 Aopp Amul Aone}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Infix "*" := Amul : A_scope.

  (** k*a1+k*a2+... == k * (a1+a2+...) *)
  Lemma fold_right_cmul : forall (l1 l2 : list A) n a,
      length l1 = n -> length l2 = n ->
      (forall i, i < n -> nth i l1 0 == a * (nth i l2 0))%A ->
      (fold_right Aadd 0 l1 == a * (fold_right Aadd 0 l2))%A.
  Proof.
    induction l1,l2; intros; simpl in *; try lia. ring.
    destruct n; try lia. rewrite (IHl1 l2 n a1); auto.
    - ring_simplify. agroup.
      specialize (H1 O); simpl in H1. rewrite H1; try easy. lia.
    - intros. specialize (H1 (S i)); simpl in H1. apply H1. lia.
  Qed.

End fold_right.


(* ===================================================================== *)
(** ** Generalized Associative Law *)
Section generalized_associative.
  Context `{AMonoid}.

  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "'\sum' a '&' l " := (fold_left Aadd l a) (at level 10).
  
  (** Generalized Associative Law *)
  (* i.e., given two expressions a1+a2+... and b1+b2+..., then 
      (a1+a2+...) + (b1+b2+...) = a1+a2+...+b1+b2+...
     It shows the associative law in a general case (not limited 3 terms) *)
  Lemma assoc_law : forall (l1 l2 : list A),
      \sum 0 & l1 + \sum 0 & l2 == \sum 0 & (l1 ++ l2).
  Proof.
    induction l1, l2; simpl; amonoid.
    - rewrite app_nil_r. easy.
    - setoid_replace a with (0 + a) by monoid.
      rewrite !fold_left_rebase_l.
      rewrite <- IHl1. simpl. amonoid.
  Qed.
End generalized_associative.


(* ===================================================================== *)
(** ** Print a list *)
Section lprint.
  Context {A : Type}.
  Definition lprint (l : list A) (p : A -> string) : string :=
    fold_left (fun s x => append s (p x)) l "".
End lprint.

(* Compute lprint [1;2;3;4;5;6;7;8;9;10] (fun n => str_alignl (nat2str n) 5). *)
(* Compute lprint [1;2;3;4;5;6] (fun n => str_alignr (nat2str n) 5). *)


(* ===================================================================== *)
(** ** Set element of a list *)
Section lset.

  Context `{Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.

  (** Set i-th element of list `l` with `x` *)
  Fixpoint lset (l : list A) (i : nat) (x : A) : list A :=
    match l, i with
    | [], _ => []
    | a :: l, 0 => x :: l
    | a :: l, S i => a :: (lset l i x)
    end.

  (** Length property *)
  Lemma lset_length : forall (l : list A) ni n x, 
      length l = n -> length (lset l ni x) = n.
  Proof.
    intros l; induction l; auto. induction ni; auto; simpl; intros.
    destruct n; auto. easy.
  Qed.

  (** Set i-th element of list `l` with a function `f` *)

  (* auxiliary function: i0 is given position, i is changing every loop *)
  Fixpoint lsetfAux (l : list A) (i0 i : nat) (f : nat -> A) : list A :=
    match l, i with
    | [], _ => []
    | a :: l, 0 => f i0 :: l
    | a :: l, S i => a :: (lsetfAux l i0 i f)
    end.

  Definition lsetf (l : list A) (i : nat) (f : nat -> A) : list A := lsetfAux l i i f.
  
  (** Length property *)
  Lemma lsetfAux_length : forall (l : list A) i n i0 f, 
      length l = n -> length (lsetfAux l i0 i f) = n.
  Proof.
    intros l; induction l; auto. destruct i; auto; simpl; intros.
    destruct n; auto. easy.
  Qed.

  Lemma lsetf_length : forall (l : list A) n i f, 
      length l = n -> length (lsetf l i f) = n.
  Proof. intros. apply lsetfAux_length; auto. Qed.

End lset.

(* Let f := fun (i : nat) => (i + 5). *)
(* Compute lsetf [1;2;3] 0 f. *)
(* Compute lsetf [1;2;3] 1 f. *)


(* ===================================================================== *)
(** ** Swap two elements *)
Section lswap.
  Context `{Equivalence A Aeq}.  Context (Azero : A).
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Notation "0" := Azero : A_scope.
  
  (** Swap i1-th and i2-th elements of list `l` *)
  Definition lswap (l : list A) (i1 i2 : nat) : list A :=
    let r := length l in
    if (i1 <? r) && (i2 <? r)
    then 
      let e1 := nth i1 l 0 in
      let e2 := nth i2 l 0 in
      lset (lset l i1 e2) i2 e1
    else l.

  Lemma lswap_length : forall l i1 i2, length (lswap l i1 i2) = length l.
  Proof.
    intros. unfold lswap.
    destruct (i1 <? length l) eqn:E1, (i2 <? length l) eqn:E2; simpl; auto.
    rewrite lset_length with (n:=length l); auto.
    rewrite lset_length with (n:=length l); auto.
  Qed.

End lswap.


(* ===================================================================== *)
(** ** lzero : a list will all elements are 0 *)
Section lzero.
  Context {A : Type}.
  
  (** A friendly name for zero list *)
  Definition lzero (Azero : A) n := repeat Azero n.

  (** lzero's length law *)
  Lemma lzero_length (Azero : A) : forall n, length (lzero Azero n) = n.
  Proof. intros. apply repeat_length. Qed.

  (** append two zero list to a zero list satisfy length relation *)
  Lemma lzero_app (Azero : A) : forall n1 n2,
      lzero Azero n1 ++ lzero Azero n2 = lzero Azero (n1 + n2).
  Proof. unfold lzero. intros. rewrite repeat_app. auto. Qed.

End lzero.

  
(* ===================================================================== *)
(** ** about "map" *)

(** map for two types *)
Section map_A_B.

  Context `{Equiv_Aeq:Equivalence A Aeq}.
  Context `{Equiv_Beq:Equivalence B Beq}.
  Infix "=A=" := (Aeq) : A_scope.
  Infix "=B=" := (Beq) : A_scope.
  Infix "=A=" := (eqlistA Aeq) : list_scope.
  Infix "=B=" := (eqlistA Beq) : list_scope.

  (** map is a proper morphism *)
  #[export] Instance map_wd :
    Proper ((Aeq ==> Beq) ==> eqlistA Aeq ==> eqlistA Beq) (@map A B).
  Proof.
    simp_proper. intros f g Hfg l1 l2. revert l2.
    induction l1,l2; intros; simpl in *; try easy. inv H. f_equiv.
    apply Hfg; auto. apply IHl1; auto.
  Qed.

  (** map_ext setoid version *)
  Lemma map_ext : forall (f g : A -> B),
      (forall a : A, (f a =B= g a)%A) -> forall l : list A, map f l =B= map g l.
  Proof.
    intros f g H l. induction l; intros; try easy.
    simpl. rewrite H,IHl. easy.
  Qed.
  
  (** map is equal and f is bijective, then the list is equal *)
  Lemma map_eq_imply_eq : forall (f : A -> B) (l1 l2 : list A),
      map f l1 =B= map f l2 ->
      Bijective f (Aeq:=Aeq) (Beq:=Beq) ->
      l1 =A= l2.
  Proof.
    intros f l1. induction l1; intros; destruct l2; simpl in *; try easy.
    apply cons_eq_iff in H. destruct H.
    constructor; auto.
    destruct H0 as [Hinj Hbij].
    apply (injective_preserve_eq (f:=f)(Beq:=Beq)); auto.
  Qed.

  (** map_ext_in_iff setoid version *)
  Lemma map_ext_in_iff : forall (f g : A -> B) (l : list A),
      map f l =B= map g l <-> (forall a : A, In a l -> (f a =B= g a)%A).
  Proof.
    intros f g l. induction l; intros; simpl; split; intros; try easy.
    - inversion H; subst. rewrite IHl in H6. destruct H0.
      + subst. easy.
      + apply H6. auto.
    - f_equiv; auto. apply IHl. auto.
  Qed.

  Context (f : A -> B).

  (** map is injective, if `f` is injective on the given list *)
  Lemma map_inj : forall (l1 l2 : list A),
      (forall a b : A, In a l1 -> In b l2 -> f a =B= f b -> a =A= b)%A ->
      map f l1 =B= map f l2 ->
      l1 =A= l2.
  Proof.
    induction l1; destruct l2; intros; simpl in *; try easy.
    inversion H0. f_equal; auto.
  Qed.

  (** map is surjective, if `f` is surjective on the given list *)
  Lemma map_surj : forall (lb : list B),
    (forall b : B, In b lb -> exists (a : A), f a =B= b)%A ->
    exists (la : list A), length la = length lb /\ map f la =B= lb.
  Proof.
    intros lb H. induction lb as [|b lb]; intros.
    - exists []. auto.
    - destruct (H b) as [a]. constructor; auto. destruct IHlb as [la].
      + intros. apply H. simpl; auto.
      + exists (a :: la). simpl. destruct H1. rewrite H0,H1,H2. easy.
  Qed.

  (* If any element `a` in list `l` satisfy `P (f a)`, then `Forall P (map f l)` hold *)
  Lemma Forall_map_forall : forall (P : B -> Prop) (l : list A),
      (forall (a : A), In a l -> P (f a)) -> Forall P (map f l).
  Proof.
    intros. induction l; simpl; auto. constructor.
    apply H. simpl; auto. apply IHl. intros. apply H. simpl; auto.
  Qed.

  (** map and repeat is communtative *)
  Lemma map_repeat : forall (a : A) n, map f (repeat a n) =B= repeat (f a) n.
  Proof. induction n; simpl; auto. f_equiv; auto. Qed.
  
  Context (Azero : A) (Bzero : B).

  (** (map f l)[i] == f (l[i]) *)
  Lemma nth_map : forall n i (l : list A),
      length l = n -> i < n ->
      (nth i (map f l) Bzero =B= f (nth i l Azero))%A.
  Proof.
    intros n i l. revert n i. induction l; intros; simpl in *. lia.
    destruct n; try lia. destruct i; try easy.
    apply IHl with (n:=n). lia. lia.
  Qed.

End map_A_B.

(** map for three types *)
Section map_A_B_C.
  Context `{Aeq : relation A} `{Beq : relation B} `{Ceq_equiv : Equivalence C Ceq}.
  Infix "==" := (eqlistA Ceq).

  (** map_map setoid version *)
  Lemma map_map : forall (f : A -> B) (g : B -> C) (l : list A),
      map g (map f l) == map (fun x : A => g (f x)) l.
  Proof. intros f g l. induction l; simpl; try easy. f_equiv; auto. Qed.

End map_A_B_C.

(** map for one type *)
Section map_A.
  Context `{Aequiv : Equivalence A Aeq}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).
  Context (f : A -> A).

  (** Extented map_id lemma, which needn't the function is a exactly format of
     "forall x, x" *)
  Lemma map_id : forall (l : list A) (H: forall a, (f a == a)%A), map f l == l.
  Proof. induction l; intros; simpl; auto. Qed.
  
  (** Extented map_id (In version) *)
  Lemma map_id_In : forall (l : list A), (forall a : A, In a l -> (f a == a)%A) -> map f l == l.
  Proof.
    induction l; intros; simpl; auto. f_equiv.
    - apply H. simpl; auto.
    - apply IHl. intros. apply H. simpl; auto.
  Qed.

  Context (Azero : A).
  Notation "0" := Azero : A_scope.
  
  (** f x = 0 -> map f = lzero *)
  Lemma map_eq_zero : forall (l : list A) n,
      (forall x : A, (f x == 0)%A) -> length l = n -> map f l == lzero 0 n.
  Proof.
    induction l; intros; simpl in *. subst. simpl. easy.
    destruct n. easy. inv H0. simpl. f_equiv; auto.
  Qed.
  
  (** Mapping is fixpoint, iff f is id *)
  Lemma map_fixpoint_imply_id : forall (l : list A), 
      map f l == l -> (forall x, In x l -> (f x == x)%A).
  Proof.
    induction l; intros; simpl in *. easy. inversion H.
    destruct H0. subst; auto. apply IHl; auto.
  Qed.

  (** Simplify of nth+map+seq *)
  Lemma nth_map_seq : forall (g : nat -> A) n m i,
      i < m -> (nth i (map g (seq n m)) 0 == g (i + n))%A.
  Proof.
    (* Tips: we need to induction on two variables to complete the proof *)
    intros. revert m i g H. induction n.
    - induction m; simpl; intros. lia. destruct i; try easy.
      rewrite <- seq_shift. rewrite map_map. rewrite IHm; try easy. lia.
    - intros. rewrite <- seq_shift. rewrite List.map_map. rewrite IHn; auto.
      f_equiv. lia.
  Qed.

  (** Simplify of map+nth+seq *)
  (* Note: the lower index of seq is 0, it could extend to any nat number later *)
  Lemma map_nth_seq  : forall n (l : list A),
      length l = n -> map (fun i => nth i l 0) (seq 0 n) == l.
  Proof.
    induction n; intros; simpl in *.
    - apply (length_zero_iff_nil (Aeq:=Aeq)) in H; subst. easy.
    - destruct l; simpl in *; try lia.
      f_equiv. rewrite <- seq_shift, map_map. rewrite IHn. easy. lia.
  Qed.

  (** Equality of map+seq, iff corresponding elements are equal *)
  Lemma map_seq_eq : forall n (f g : nat -> A),
      map f (seq 0 n) == map g (seq 0 n) <-> (forall i, i < n -> (f i == g i)%A).
  Proof.
    intros; split; intros.
    - rewrite map_ext_in_iff in H. apply H. apply in_seq. lia.
    - apply map_ext_in_iff. intros. apply H. apply in_seq in H0. lia.
  Qed.

End map_A.


(* ===================================================================== *)
(** ** map two lists to a list *)
Section map2.
  Context {A B C :Type} {Aeq:relation A} {Beq:relation B} {Ceq:relation C}.
  Context `{Ceq_equiv : Equivalence C Ceq}.
  Infix "=C=" := Ceq : A_scope.
  Infix "=C=" := (eqlistA Ceq) : list_scope.
  Context (f : A -> B -> C).
  Context (f_wd : Proper (Aeq ==> Beq ==> Ceq) f).
  
  (** map operation to two list *)
  Fixpoint map2 (l1 : list A) (l2 : list B) : list C :=
    match l1, l2 with
    | x1 :: t1, x2 :: t2 => (f x1 x2) :: (map2 t1 t2)
    | _, _ => []
    end.

  #[export] Instance map2_wd : Proper (eqlistA Aeq ==> eqlistA Beq ==> eqlistA Ceq) map2.
  Proof.
    intros a1. induction a1.
    - intros a2 Ha b1 b2 Hb. destruct b1,a2,b2; try easy.
    - intros a2 Ha b1 b2 Hb. destruct b1,a2,b2; try easy.
      simpl. inversion Ha. inversion Hb. subst. f_equiv.
      + apply f_wd; auto.
      + apply IHa1; auto.
  Qed.
  
  (** length of map2 *)
  Lemma map2_length : forall (l1 : list A) (l2 : list B) n,
      length l1 = n -> length l2 = n -> length (map2 l1 l2) = n.
  Proof. 
    induction l1,l2; simpl; auto. intros. destruct n; simpl; auto. easy.
  Qed.
  
  (** map2 to two lists could be separated by two segments with same length *)
  Lemma map2_app : forall (la1 la2 : list A) (lb1 lb2 : list B),
      length la1 = length lb1 -> length la2 = length lb2 ->
      map2 (la1 ++ la2) (lb1 ++ lb2) =C= (map2 la1 lb1) ++ (map2 la2 lb2).
  Proof.
    induction la1, lb1; intros; simpl; auto; simpl in H; try easy. f_equiv; auto.
  Qed.
  
  (** map2 [] l = [] *)
  Lemma map2_nil_l : forall l, map2 [] l =C= [].
  Proof. destruct l; easy. Qed.

  (** map2 l [] = [] *)
  Lemma map2_nil_r : forall l, map2 l [] =C= [].
  Proof. destruct l; easy. Qed.

  Context (Azero : A) (Bzero : B) (Czero : C).

  (** nth (map2 f l1 l2) i = f (nth l1 i) (nth l2 i) *)
  Lemma nth_map2 : forall n i (l1 : list A) (l2 : list B) (a : A)(b : B)(c : C),
      length l1 = n -> length l2 = n -> i < n ->
      (nth i (map2 l1 l2) c =C= f (nth i l1 a) (nth i l2 b))%A.
  Proof.
    intros n i l1. revert n i.
    induction l1,l2; intros; simpl in *; destruct i; try lia; try easy.
    destruct n; try lia. apply IHl1 with (n:=n); lia.
  Qed.
  
End map2.

Hint Resolve map2_length : list.


(* ===================================================================== *)
(** ** map2 on dlist *)
Section map2_dlist.
  Context {A B C : Type} `{Ceq : relation C}.
  Context `{Cequiv : Equivalence C Ceq}.
  Infix "==" := (eqlistA (eqlistA Ceq)).
  Variable f : A -> B -> C.
  
  (** tail of map2 to dlist, equal to map2 to tail part of original dlists *)
  Lemma tail_map2_dlist : forall dl1 dl2,
      tl (map2 (map2 f) dl1 dl2) == map2 (map2 f) (tl dl1) (tl dl2).
  Proof.
    destruct dl1, dl2; simpl; try easy. rewrite map2_nil_r. easy.
  Qed.

End map2_dlist.


(* ===================================================================== *)
(** ** map2 properties with same base type *)
Section map2_sametype.
  Context `{HAMonoid : AMonoid}.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** nth (map2 f l1 l2) i = f (nth l1 i) (nth l2 i) *)
  Lemma nth_map2_same : forall (l1 l2 : list A) i (a : A),
    i < length l1 -> i < length l2 -> length l1 = length l2 ->
    (nth i (map2 Aadd l1 l2) a == nth i l1 a + nth i l2 a)%A.
  Proof. intros. eapply nth_map2; auto. Qed.
    
  (** (l1 . l2) . l3 = l1 . (l2 . l3) *)
  Lemma map2_assoc : forall (l1 l2 l3 : list A),
      map2 Aadd (map2 Aadd l1 l2) l3 == map2 Aadd l1 (map2 Aadd l2 l3).
  Proof. induction l1,l2,l3; simpl; try easy. f_equiv; amonoid. Qed.

  (** l1 . l2 = l2 . l1 *)
  Lemma map2_comm : forall (l1 l2 : list A), map2 Aadd l1 l2 == map2 Aadd l2 l1.
  Proof. induction l1,l2; simpl; try easy. f_equiv; amonoid. Qed.

  (** map2 lzero l = l *)
  Lemma map2_zero_l : forall l n, length l = n -> map2 Aadd (lzero 0 n) l == l.
  Proof. induction l,n; intros; simpl in *; try easy. f_equiv; auto; amonoid. Qed.

  (** map2 l lzero = l *)
  Lemma map2_zero_r : forall l n, length l = n -> map2 Aadd l (lzero 0 n) == l.
  Proof. induction l,n; intros; simpl in *; try easy. f_equiv; auto; amonoid. Qed.
  
  (** map2 over map is homorphism *)
  (* In fact, I don't know how to naming this property yet. *)
  Lemma map2_map_hom :
    forall l1 l2 (g : A -> A) (H : forall a b : A, (g (a + b) == (g a) + (g b))%A),
      map2 Aadd (map g l1) (map g l2) == map g (map2 Aadd l1 l2).
  Proof. induction l1,l2; intros; simpl in *; try easy. f_equiv; auto. agroup. Qed.
  

  Context `{AG:AGroup A Aeq Aadd 0 Aopp}.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (-b)).
  Infix "-" := Asub : A_scope.

  (** l1 - l2 == - (l2 - l1) *)
  Lemma map2_sub_comm : forall (l1 l2 : list A),
      map2 Asub l1 l2 == map Aopp (map2 Asub l2 l1).
  Proof. induction l1,l2; intros; simpl in *; try easy. f_equiv; agroup. Qed.

  (** (l1 - l2) - l3 == (l1 - l3) - l2 *)
  Lemma map2_sub_perm : forall (l1 l2 l3 : list A),
      map2 Asub (map2 Asub l1 l2) l3 == map2 Asub (map2 Asub l1 l3) l2.
  Proof. induction l1,l2,l3; intros; simpl in *; try easy. f_equiv; agroup. Qed.
  
  (** (l1 - l2) - l3 == l1 - (l2 + l3) *)
  Lemma map2_sub_assoc : forall (l1 l2 l3 : list A),
      map2 Asub (map2 Asub l1 l2) l3 == map2 Asub l1 (map2 Aadd l2 l3).
  Proof. induction l1,l2,l3; intros; simpl in *; try easy. f_equiv; agroup. Qed.

  (** 0 - l == - l *)
  Lemma map2_sub_zero_l : forall l n, 
      length l = n -> map2 Asub (lzero 0 n) l == map Aopp l.
  Proof. induction l,n; intros; simpl in *; try easy. f_equiv; auto; agroup. Qed.
  
  (** l - 0 == l *)
  Lemma map2_sub_zero_r : forall l n, 
      length l = n -> map2 Asub l (lzero 0 n) == l.
  Proof. induction l,n; intros; simpl in *; try easy. f_equiv; auto; agroup. Qed.
  
  (** l - l = 0 *)
  Lemma map2_sub_self : forall l n, length l = n -> map2 Asub l l == (lzero 0 n).
  Proof. induction l,n; intros; simpl in *; try easy. f_equiv; auto; agroup. Qed.

End map2_sametype.

(** map2 with map of two components *)
Section map2_map_map.
  Context {A B : Type}.
  Context {Beq : relation B}.
  Infix "==" := (Beq) : A_scope.
  Infix "==" := (eqlistA Beq) : list_scope.

  Lemma map2_map_map :
    forall (f1 f2 g : A -> B) (h : B -> B -> B)
      (H : forall x, (h (f1 x) (f2 x) == g x)%A)
      (l : list A),
      map2 h (map f1 l) (map f2 l) == map g l.
  Proof. induction l; simpl; auto. Qed.

End map2_map_map.


(* ===================================================================== *)
(** ** concatenation of list *)
Section concat.

  (** Length of concat operation *)
  Lemma concat_length : forall {A} (l : dlist A),
      length (concat l) = fold_left add (map (@length A) l) 0.
  Proof.
    intros A l. induction l; simpl; auto. rewrite app_length. rewrite IHl.
    replace (Datatypes.length a) with (0 + Datatypes.length a) at 2 by lia.
    rewrite fold_left_rebase_l. lia.
  Qed.

End concat.


(* ===================================================================== *)
(** ** Convert between list and natural-number-index-function *)
Section f2l_l2f.
  Context `{Aequiv : Equivalence A Aeq} {Azero : A}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Notation "0" := Azero : A_scope.

  Definition f2l (n : nat) (f : nat -> A) : list A := map f (seq 0 n).
  Definition l2f (n : nat) (l : list A) : nat -> A := fun i => nth i l 0.

  Lemma f2l_length : forall n f, length (f2l n f) = n.
  Proof. intros. unfold f2l. rewrite map_length, seq_length. auto. Qed.

  (** (f2l f)[i] = f i *)
  Lemma nth_f2l : forall {n} f a i, i < n -> (nth i (f2l n f) a == f i)%A.
  Proof. intros. unfold f2l. rewrite nth_map_seq; auto. f_equiv; lia. Qed.

  Lemma f2l_inj : forall n (f1 f2 : nat -> A),
      f2l n f1 == f2l n f2 -> (forall i, i < n -> (f1 i == f2 i)%A).
  Proof.
    intros. unfold f2l in *. rewrite map_ext_in_iff in H. apply H.
    apply in_seq; auto. lia.
  Qed.

  Lemma l2f_inj : forall n (l1 l2 : list A),
      (forall i, i < n -> ((l2f n l1) i == (l2f n l2 i))%A) ->
      length l1 = n -> length l2 = n -> l1 == l2.
  Proof. intros. unfold l2f in *. apply list_eq_iff_nth in H; auto. Qed.
  
  Lemma f2l_l2f : forall l {n}, length l = n -> f2l n (l2f n l) == l.
  Proof.
    intros. apply (list_eq_iff_nth 0 n); auto.
    apply f2l_length. intros. rewrite nth_f2l; easy.
  Qed.

  Lemma l2f_f2l : forall f n i, i < n -> (l2f n (f2l n f) i == f i)%A.
  Proof. intros. unfold l2f. rewrite nth_f2l; easy. Qed.

  Lemma f2l_surj : forall n (l : list A), length l = n -> exists (f : nat -> A), f2l n f == l.
  Proof. intros. exists (l2f n l). apply f2l_l2f; auto. Qed.

  Lemma l2f_surj : forall n (f : nat -> A),
    exists (l : list A), (forall i, i < n -> (l2f n l) i == f i)%A.
  Proof. intros. exists (f2l n f). intros. apply l2f_f2l; auto. Qed.

End f2l_l2f.

Section test.
  (** [1;2;3] *)
  Let f := fun i => i + 1.
  Let l := f2l 3 f.
  (* Compute l. *)

  Let g := @l2f _ 0 3 l.
  (* Compute (g 0, g 1, g 2). *)
End test.  


(* ===================================================================== *)
(** ** Addition, Opposition and Subtraction of list *)
Section ladd_opp_sub.

  (* Tips: these old codes are replaced with Typeclass. *)
  (* Variable A : Type. *)
  (* Variable Azero : A. *)
  (* Variable add : A -> A -> A. *)
  (* Variable add_comm : forall a b, add a b = add b a. *)
  (* Variable add_0_l : forall a, add Azero a = a. *)
  (* Variable opp : A -> A. *)
  (* Variable sub : A -> A -> A. *)
  (* Variable sub_comm : forall a b, sub a b = opp (sub b a). *)
  (* Variable sub_assoc1 : forall a b c, sub (sub a b) c = sub a (sub c b). *)
  (* Variable sub_assoc2 : forall a b c, sub (sub a b) c = sub a (add b c). *)
  (* Variable sub_0_l : forall a, sub Azero a = opp a. *)
  (* Variable sub_0_r : forall a, sub a Azero = a. *)
  (* Variable sub_self : forall a, sub a a = Azero. *)

  Context `{AG:AGroup A Aeq Aadd Azero Aopp}.
  Notation Asub := (fun a b => Aadd a (Aopp b)).
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  (** l1 + l2 *)
  Notation ladd := (map2 Aadd).
  Infix "+" := ladd : list_scope.
  
  (** - l *)
  Notation lopp := (map Aopp).
  Notation "- l" := (lopp l) : list_scope.
  
  (** l1 - l2 *)
  Notation lsub := (map2 Asub).
  Infix "-" := lsub : list_scope.

  (** invariant for length of ladd *)
  Lemma ladd_length : forall l1 l2 n,
      length l1 = n -> length l2 = n -> length (l1 + l2) = n.
  Proof. intros. apply map2_length; auto. Qed.
  
  (** l1 + l2 == l2 + l1 *)
  Lemma ladd_comm : forall l1 l2, l1 + l2 == l2 + l1.
  Proof. apply map2_comm; auto. Qed.
  
  (** [] + l == [] *)
  Lemma ladd_nil_l : forall l, [] + l == [].
  Proof. apply map2_nil_l. Qed.
  
  (** l + [] == [] *)
  Lemma ladd_nil_r : forall l, l + [] == [].
  Proof. apply map2_nil_r. Qed.
  
  (** 0 + l == l *)
  Lemma ladd_zero_l : forall l n, length l = n -> (lzero Azero n) + l == l.
  Proof. apply map2_zero_l. Qed.
  
  (** l + 0 == l *)
  Lemma ladd_zero_r : forall l n, length l = n -> l + (lzero Azero n) == l.
  Proof. apply map2_zero_r. Qed.

  (** l1 - l2 == - (l2 - l1) *)
  Lemma lsub_comm : forall (l1 l2 : list A), l1 - l2 == - (l2 - l1).
  Proof. intros. apply map2_sub_comm. Qed.
  
  (** (l1 - l2) - l3 == (l1 - l3) - l2 *)
  Lemma lsub_perm : forall (l1 l2 l3 : list A),
      (l1 - l2) - l3 == (l1 - l3) - l2.
  Proof. apply map2_sub_perm; apply AG. Qed.
  
  (** (l1 - l2) - l3 == l1 - (l2 + l3) *)
  Lemma lsub_assoc : forall (l1 l2 l3 : list A),
      (l1 - l2) - l3 == l1 - (l2 + l3).
  Proof. apply map2_sub_assoc. Qed.
  
  (** 0 - l == - l *)
  Lemma lsub_zero_l : forall l n, length l = n -> (lzero Azero n) - l == - l.
  Proof. apply map2_sub_zero_l; apply AG. Qed.
  
  (** l - 0 == l *)
  Lemma lsub_zero_r : forall l n, length l = n -> l - (lzero Azero n) == l.
  Proof. apply map2_sub_zero_r; apply AG. Qed.
  
  (** l - l == 0 *)
  Lemma lsub_self : forall l n, length l = n -> l - l == (lzero Azero n).
  Proof. apply map2_sub_self; apply AG. Qed.
  
End ladd_opp_sub.


(* ===================================================================== *)
(** ** constant multiplication of list *)
Section lcmul.
  (* Variable A : Type. *)
  (* Variable Azero Aone : A. *)
  (* Variable mul : A -> A -> A. *)
  (* Infix "*" := mul. *)
  (* Variable mul_comm : forall a b, a * b = b * a. *)
  (* Variable mul_0_l : forall a, Azero * a = Azero. *)
  (* Variable Aeqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}. *)
  (* Variable mul_1_l : forall a : A, Aone * a = a. *)
  (* Variable mul_cancel_r : forall r1 r2 r : A,  *)
  (*     r <> Azero -> r1 * r = r2 * r -> r1 = r2.  *)

  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "*" := Amul : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.

  (** a * l *)
  Notation lcmul := (fun a l => map (fun x => a * x) l).
  
  (** cmul keep its length *)
  Lemma lcmul_length : forall a l n, length l = n -> length (lcmul a l) = n.
  Proof. intros. simpl. rewrite map_length; auto. Qed.
  
  (** a * (x :: l) = (a * x) :: (a * l) *)
  Lemma lcmul_cons : forall a x l, (lcmul a (x :: l) == (Amul a x) :: (lcmul a l))%list.
  Proof. intros. easy. Qed.
  
  (** a * [] == [] *)
  Lemma lcmul_nil : forall a, lcmul a [] == [].
  Proof. intros. easy. Qed.
  
  (** a * 0 = 0 *)
  Lemma lcmul_zero_r : forall a n, (lcmul a (lzero Azero n) == lzero Azero n)%list.
  Proof. intros. rewrite map_repeat. unfold lzero. f_equiv. ring. Qed.

  Context `{HField:Field A Aeq Aadd 0 Aopp Amul 1 Ainv}.
  Add Field field_inst : (make_field_theory HField).
  Context {AeqDec : Dec Aeq}.

  (** k * l == l -> k == 1 \/ l == 0 *)
  Lemma lcmul_eq_imply_k1_or_lzero : 
    forall (l : list A) {n} (Hl : length l = n) (k : A),
      lcmul k l == l -> ((k == 1)%A \/ l == lzero 0 n).
  Proof.
    induction l; intros; simpl in *; subst; auto. inv H. simpl.
    apply IHl with (n:=length l) in H5; auto. destruct H5; auto.
    apply field_mul_eq_imply_a1_or_b0 in H3. destruct H3; auto.
  Qed.

  (** k * l == 0 -> k == 0 \/ l == 0 *)
  Lemma lcmul_eq0_imply_k0_or_lzero : 
    forall (l : list A) {n} (Hl : length l = n) (k : A),
      lcmul k l == lzero 0 n -> ((k == 0)%A \/ l == lzero 0 n).
  Proof.
    induction l; intros; simpl in *; subst; simpl in *; auto. inv H.
    apply IHl in H5; auto. destruct H5; auto.
    apply field_mul_eq0_iff in H3. destruct H3; auto.
  Qed.
  
End lcmul.


(* ===================================================================== *)
(** ** product of two lists *)
Section ldot.
  
  Context `{HARing:ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).

  Notation ladd := (map2 Aadd).
  Notation lopp := (map Aopp).
  Notation lcmul := (fun a l => map (fun x => a * x) l).
  
  (** dot product, marked as l1 . l2 *)
  Definition ldot (l1 l2 : list A) : A :=
    fold_right Aadd Azero (map2 Amul l1 l2).

  (** map is respect to aeq *)
  #[export] Instance ldot_wd : Proper (eqlistA Aeq ==> eqlistA Aeq ==> Aeq) ldot.
  Proof. simp_proper. intros. unfold ldot. rewrite H,H0. easy. Qed.
  
  (** l1 . l2 == l2 . l1 *)
  Lemma ldot_comm : forall (l1 l2 : list A), (ldot l1 l2 == ldot l2 l1)%A.
  Proof. intros. unfold ldot. rewrite map2_comm. easy. Qed.
  
  (** [] . l == 0 *)
  Lemma ldot_nil_l : forall (l : list A), (ldot nil l == Azero)%A.
  Proof. intros. destruct l; simpl; try easy. Qed.
  
  (** l . [] == 0 *)
  Lemma ldot_nil_r : forall (l : list A), (ldot l nil == Azero)%A.
  Proof. intros. destruct l; simpl; try easy. Qed.

  (** ldot cons *)
  Lemma ldot_cons : forall l1 l2 x1 x2,
      (ldot (x1 :: l1) (x2 :: l2) == (x1 * x2) + (ldot l1 l2))%A.
  Proof. induction l1,l2; simpl; intros; try easy. Qed.
  
  (** lzero . l == 0 *)
  Lemma ldot_zero_l : forall l n, (ldot (lzero Azero n) l == Azero)%A.
  Proof.
    induction l,n; simpl; intros; try easy. rewrite ldot_cons.
    rewrite IHl. ring.
  Qed.
  
  (** l . lzero == 0 *)
  Lemma ldot_zero_r : forall l n, (ldot l (lzero Azero n) == Azero)%A.
  Proof. intros. rewrite ldot_comm. apply ldot_zero_l. Qed.
  
  (** l1 . (l2 + l3) == l1.l2 + l1.l3 *)
  Lemma ldot_ladd_r : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (ldot l1 (ladd l2 l3) == (ldot l1 l2) + (ldot l1 l3))%A.
  Proof.
    induction l1,l2,l3; simpl; intros; subst; try (cbv;ring); try easy.
    rewrite ?ldot_cons. ring_simplify.
    ring_simplify. (* Tips, ring has no effect *)
    pose proof (ringAddAG HARing). agroup. (* Tips, our tactic run well *)
    eapply IHl1; auto.
  Qed.
  
  (** (l1 + l2) . l3 == l1.l3 + l2.l3 *)
  Lemma ldot_ladd_l : forall l1 l2 l3 r,
      length l1 = r -> length l2 = r -> length l3 = r ->
      (ldot (ladd l1 l2) l3 == (ldot l1 l3) + (ldot l2 l3))%A.
  Proof.
    intros. rewrite !(ldot_comm _ l3). rewrite <- ldot_ladd_r; auto; try lia. easy.
  Qed.

  (** (- l1) * l2 == - (l1 * l2) *)
  Lemma ldot_lopp_l : forall l1 l2 r,
      length l1 = r -> length l2 = r ->
      (ldot (lopp l1) l2 == Aopp (ldot l1 l2))%A.
  Proof.
    induction l1,l2; simpl in *; intros; subst; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.

  (** l1 * (- l2) = - (l1 * l2) *)
  Lemma ldot_lopp_r : forall l1 l2 r,
      length l1 = r -> length l2 = r ->
      (ldot l1 (lopp l2) == Aopp (ldot l1 l2))%A.
  Proof.
    induction l1,l2; simpl in *; intros; subst; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1 with (r:=length l1); auto. ring.
  Qed.
  
  (** (x * l1) . l2 == x * (l1 . l2) *)
  Lemma ldot_lcmul_l : forall l1 l2 x,
      (ldot (lcmul x l1) l2 == x * (ldot l1 l2))%A.
  Proof.
    induction l1,l2; intros; simpl; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1. ring.
  Qed.

  (** l1 . (x * l2) == x * (l1 . l2) *)
  Lemma ldot_lcmul_r : forall l1 l2 x,
      (ldot l1 (lcmul x l2) == x * (ldot l1 l2))%A.
  Proof.
    induction l1,l2; intros; simpl; try (cbv; ring).
    rewrite ?ldot_cons. rewrite IHl1. ring.
  Qed.

End ldot.


(* ===================================================================== *)
(** ** list for identity matrix *)
Section lunit.
  Context `{AR:ARing}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  
  (** create a list which its length is n and all elements are 0 excepts i-th is 1. *)
  Fixpoint lunit (n i : nat) : list A :=
    match n, i with
    | 0, _ => []
    | S n, 0 => 1 :: (repeat 0 n)
    | S n, S i => 0 :: (lunit n i)
    end.

  (* Compute lunit 0 2. (* [] *) *)
  (* Compute lunit 3 0. (* [1;0;0] *) *)
  (* Compute lunit 3 1. (* [0;1;0] *) *)
  (* Compute lunit 3 2. (* [0;0;1] *) *)
  (* Compute lunit 3 3. (* [0;0;0] *) *)

  Lemma lunit_length : forall n i, length (lunit n i) = n.
  Proof.
    induction n; auto. destruct i; simpl; auto. rewrite repeat_length. auto.
  Qed.
  
  (** lunit(n,i) [i] = 1 *)
  Lemma nth_lunit_eq : forall n i, i < n -> nth i (lunit n i) 0 = 1.
  Proof.
    induction n; try easy. destruct i; simpl; try easy.
    intros; apply IHn. lia.
  Qed.
  
  (** lunit(n,i) [j] = 0, when j <> i *)
  Lemma nth_lunit_neq : forall n i j, j <> i -> nth j (lunit n i) 0 = 0.
  Proof.
    induction n; try easy; simpl; intros.
    - destruct j; easy.
    - destruct i,j; simpl; try easy. apply nth_repeat. apply IHn. auto.
  Qed.
  
End lunit.

Hint Resolve lunit_length : list.


(* ===================================================================== *)
(** ** Convert list to a list with given length *)
Section listN.
  Context `{M:Monoid}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).
  
  Fixpoint listN (l : list A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n' => (hd Azero l) :: (listN (tl l) n')
    end.
  
  Lemma listN_length : forall (l : list A) (n : nat), length (listN l n) = n.
  Proof. intros l n. revert l. induction n; intros; simpl; auto. Qed.
  
  Lemma listN_eq : forall (l : list A), listN l (length l) == l.
  Proof. induction l; simpl; auto. f_equiv; auto. Qed.

End listN.


(* ===================================================================== *)
(** ** Find non-zero element from a list *)
Section listFirstNonZero.
  Context `{Dec} (Azero : A).
  
  (* Find the index of first non-zero element, if nothing return none. *)
  Definition listFirstNonZero (l : list A) : option nat :=
    let fix F (l : list A) (i : nat) : option nat :=
      match l with
      | [] => None
      | hl :: tl =>
          if dec hl Azero
          then F tl (S i)
          else Some i
      end in
    F l 0.

End listFirstNonZero.

Section test.
  (* Compute listFirstNonZero 0 [0;0;1;2;3]. *)
End test.


(* ===================================================================== *)
(** ** Sub list *)
Section sublist.
  Context `{Equivalence A Aeq}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq).
  Context (Azero : A).

  Definition sublist {A} (l : list A) (lo n : nat) : list A :=
    firstn n (skipn lo l).

  Lemma sublist_overflow : forall (l : list A) lo n,
      length l <= lo -> sublist l lo n == [].
  Proof.
    intros. unfold sublist. rewrite skipn_all2; try lia. rewrite firstn_nil. easy.
  Qed.
  
  Lemma sublist_Sn : forall (l : list A) lo n,
      sublist l lo (S n) ==
        if length l <=? lo
        then []
        else (nth lo l Azero) :: sublist l (S lo) n.
  Proof.
    induction l; intros; unfold sublist in *; simpl in *.
    - destruct lo; auto.
    - destruct lo; simpl; auto. easy.
  Qed.

  Lemma sublist_cons : forall (a : A) (l : list A) lo n,
      sublist (a :: l) lo (S n) ==
        if lo =? 0
        then a :: sublist l 0 n
        else sublist l (pred lo) (S n).
  Proof. intros. unfold sublist. simpl. destruct lo; simpl; easy. Qed.
  
End sublist.

Section test.
  (* Compute sublist [1;2;3;4;5] 1 3. *)
End test.



(* ##################################################################### *)
(** * dlist (list of list) *)

Open Scope dlist_scope.


(* ===================================================================== *)
(** ** Setoid equal of list *)
Section listSetoidEq.
  Context `{Equivalence A Aeq}.

  (** Two list `l1` and `l2` are setoid equal under `Aeq` relation *)
  Notation listSetoidEq := (eqlistA Aeq).
  
  (** Two dlist `d1` and `d2` are setoid equal under `Aeq` relation *)
  Notation dlistSetoidEq := (eqlistA (eqlistA Aeq)).

  (* Variable l1 l2 : list A. *)
  (* Check listSetoidEq l1 l2. *)

  (* Variable dl1 dl2 : dlist A. *)
  (* Check dlistSetoidEq dl1 dl2. *)
End listSetoidEq.

(* ===================================================================== *)
(** ** width of a dlist (dlist A) *)
Section width.
  
  Context {A : Type}.

  (** A proposition that every list of a dlist has same length *)
  Definition width {A : Type} (dl : dlist A) (n : nat) : Prop :=
    Forall (fun l => length l = n) dl.

  (** width property should be kept by its child structure *)
  Lemma cons_width_iff : forall (l : list A) dl n,
      width (l :: dl) n <-> length l = n /\ width dl n.
  Proof.
    intros. split; intros; inversion H; auto.
    constructor; auto.
  Qed.

  (** width property should be kept by every child element *)
  Lemma width_imply_in_length : forall (l : list A) dl n, 
      width dl n -> In l dl -> length l = n.
  Proof.
    intros. induction dl. inv H0.
    apply cons_width_iff in H; destruct H. apply in_inv in H0. destruct H0.
    + subst. auto.
    + apply IHdl; auto.
  Qed.

  (** app keep width *)
  Lemma app_width : forall (dl1 : dlist A) dl2 n, 
      width (dl1 ++ dl2) n <-> width dl1 n /\ width dl2 n.
  Proof.
    unfold width in *.
    induction dl1; intros; split; intros; simpl in *; inv H; auto.
    - apply IHdl1 in H3 as []. split; auto.
    - inv H0. constructor; auto. apply IHdl1. auto.
  Qed.

  (** rev keep width *)
  Lemma rev_width : forall (dl : dlist A) n, width (rev dl) n -> width dl n.
  Proof.
    unfold width in *.
    induction dl; simpl; intros; auto.
    apply app_width in H. destruct H. inv H0. constructor; auto.
  Qed.

  (** repeat keep width *)
  Lemma repeat_width : forall (l : list A) n k,
      length l = k -> width (repeat l n) k.
  Proof.
    unfold width. induction n; intros; simpl; auto.
  Qed.

  (** firstn keep width *)
  Lemma firstn_width : forall (dl : dlist A) c n, width dl c -> width (firstn n dl) c.
  Proof.
    induction dl; intros; destruct n; simpl; auto. constructor.
    inv H. constructor; auto. apply IHdl. auto.
  Qed.
    
  (** skipn keep width *)
  Lemma skipn_width : forall (dl : dlist A) c n, width dl c -> width (skipn n dl) c.
  Proof.
    induction dl; intros; destruct n; simpl; auto. apply IHdl. inv H; auto.
  Qed.

  (** i-th row has same length *)
  Lemma dlist_nth_length : forall i c (dl : dlist A) l,
      i < length dl -> width dl c -> length (nth i dl l) = c.
  Proof.
    unfold width. intros i c dl. revert i c.
    induction dl; intros; simpl in *. lia.
    inv H0. destruct i; auto. apply IHdl; auto. lia.
  Qed.

  (** i-th row has zero length if index overflow *)
  Lemma dlist_nth_length_overflow : forall i (dl : dlist A) l,
      i >= length dl -> length (nth i dl l) = length l.
  Proof.
    intros i dl. revert i.
    induction dl; intros; simpl in *.
    - destruct i; auto.
    - destruct i. lia. assert (i >= length dl). lia. apply IHdl; auto.
  Qed.
  
  (** map width law *)
  Lemma width_map : forall (f: nat -> list A) (rowIdxs : list nat) c,
      (forall i, length (f i) = c) -> width (map f rowIdxs) c.
  Proof.
    unfold width. intros f idxs. induction idxs; simpl; auto.
  Qed.

End width.


(* ===================================================================== *)
(** ** Equalities of dlist *)
Section dlist_eq.
  Context `{Aequiv : Equivalence A Aeq}.
  Context `{Azero:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).

  (** ** Length of a empty dlist *)
  Lemma dlist_h0_iff : forall (dl : dlist A), 
      length dl = 0 -> dl == nil.
  Proof.
    destruct dl; simpl; auto. intros H; easy.
  Qed.
  
  (** Two dlist equal iff corresponded elements all equal *)
  Lemma dlist_eq_iff_nth_nth :
    forall r c (dl1 dl2 : dlist A)
      (H1 : length dl1 = r) (H2 : length dl2 = r)
      (H3 : width dl1 c) (H4 : width dl2 c),
      dl1 == dl2 <->
        (forall (i j : nat), i < r -> j < c -> 
                      (nth j (nth i dl1 []) Azero == nth j (nth i dl2 []) Azero))%A.
  Proof.
    intros; split; intros.
    - rewrite H. easy.
    - apply (list_eq_iff_nth [] _ dl1 dl2 H1 H2); intros.
      rewrite (list_eq_iff_nth) with (n:=c); auto.
      + apply dlist_nth_length; auto; lia.
      + apply dlist_nth_length; auto; lia.
  Qed.

  (** dlist_eq is decidable *)
  Context {AeqDec : Dec Aeq}.
  Lemma dlist_eq_dec : forall (dl1 dl2 : dlist A), {dl1 == dl2} + {~(dl1 == dl2)}.
  Proof. apply list_eq_dec. Qed.

End dlist_eq.


(* ===================================================================== *)
(** ** Print a dlist *)
Section dlprt.
  Context {A : Type}.

  Definition dlprint (dl : dlist A) (p : A -> string) : string :=
    let f := (fun s l => String.append s (String.append (lprint l p) strNewline)) in
    fold_left f dl "".
End dlprt.

(* Compute dlprint [[1;2;3];[4;5;6]] (fun n => str_alignl (nat2str n) 5). *)
(* Compute dlprint [[1;2;3];[4;5;6]] (fun n => str_alignr (nat2str n) 5). *)


(* ===================================================================== *)
(** ** nnth : that is nth of nth of dlist *)
Section dlnth.
  Context {A} {Azero : A}.

  (* Notation "dl ! i ! j" := (nth j (nth i dl []) Azero). *)

End dlnth.


(* ===================================================================== *)
(** ** Split a dlist with given length using `nth` *)

Section dlist2elems.
  Context {A} {Azero : A}.
  Notation "dl ! i ! j" :=
    (nth j (nth i dl []) Azero) (at level 2, i,j at next level).

  (* 1x1 matrix *)
  Lemma dlist2elems_1_1 : forall (d : dlist A),
      length d = 1 -> width d 1 -> d = [[d!0!0]].
  Proof.
    intros. repeat (destruct d; simpl in *; try lia); repeat f_equal.
    apply list2elems_1; auto. inv H0; auto.
  Qed.
  
  (* 2x2 matrix *)
  Lemma dlist2elems_2_2 : forall (d : dlist A),
      length d = 2 -> width d 2 -> d = [[d!0!0; d!0!1]; [d!1!0; d!1!1]].
  Proof.
    intros. repeat (destruct d; simpl in *; try lia); repeat f_equal.
    apply list2elems_2; auto. inv H0; auto.
    apply list2elems_2; auto. inv H0; auto. inv H4; auto.
  Qed.

  (* 3x3 matrix *)
  Lemma dlist2elems_3_3 : forall (d : dlist A),
      length d = 3 -> width d 3 ->
      d = [[d!0!0; d!0!1; d!0!2];
           [d!1!0; d!1!1; d!1!2];
           [d!2!0; d!2!1; d!2!2]].
  Proof.
    intros. repeat (destruct d; simpl in *; try lia); repeat f_equal.
    apply list2elems_3; auto. inv H0; auto.
    apply list2elems_3; auto. inv H0; auto. inv H4; auto.
    apply list2elems_3; auto. inv H0; auto. inv H4; auto. inv H5; auto.
  Qed.

  (* 4x3 matrix (This demo shows that a rectangle matrix is supported also) *)
  Lemma dlist2elems_4_3 : forall (d : dlist A),
      length d = 4 -> width d 3 ->
      d = [[d!0!0; d!0!1; d!0!2];
           [d!1!0; d!1!1; d!1!2];
           [d!2!0; d!2!1; d!2!2];
           [d!3!0; d!3!1; d!3!2]].
  Proof.
    intros. repeat (destruct d; simpl in *; try lia); repeat f_equal.
    apply list2elems_3; auto. inv H0; auto.
    apply list2elems_3; auto. inv H0; auto. inv H4; auto.
    apply list2elems_3; auto. inv H0; auto. inv H4; auto. inv H5; auto.
    apply list2elems_3; auto. inv H0; auto. inv H4; auto. inv H5; auto. inv H6; auto.
  Qed.

  (* 4x4 matrix *)
  Lemma dlist2elems_4_4 : forall (d : dlist A),
      length d = 4 -> width d 4 ->
      d = [[d!0!0; d!0!1; d!0!2; d!0!3];
           [d!1!0; d!1!1; d!1!2; d!1!3];
           [d!2!0; d!2!1; d!2!2; d!2!3];
           [d!3!0; d!3!1; d!3!2; d!3!3]].
  Proof.
    intros. repeat (destruct d; simpl in *; try lia); repeat f_equal.
    apply list2elems_4; auto. inv H0; auto.
    apply list2elems_4; auto. inv H0; auto. inv H4; auto.
    apply list2elems_4; auto. inv H0; auto. inv H4; auto. inv H5; auto.
    apply list2elems_4; auto. inv H0; auto. inv H4; auto. inv H5; auto. inv H6; auto.
  Qed.

End dlist2elems.


(* ===================================================================== *)
(** ** a dlist with same element nil *)
Section dnil.
  Context `{M:Monoid}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** a dlist that every list is nil *)
  Fixpoint dnil n : dlist A :=
    match n with
    | O => nil
    | S n' => nil :: (dnil n')
    end.

  (** dnil's length law *)
  Lemma dnil_length : forall n, length (dnil n) = n.
  Proof. induction n; simpl; auto. Qed.

  (** dnil's width law *)
  Lemma dnil_width : forall n, width (dnil n) 0.
  Proof. unfold width; induction n; simpl; auto. Qed.
  
  (** dnil equal to append two child dnil *)
  Lemma dnil_app : forall n1 n2, dnil (n1 + n2) == dnil n1 ++ dnil n2.
  Proof.
    induction n1,n2; simpl; try easy.
    - rewrite app_nil_r. rewrite Nat.add_0_r. easy.
    - rewrite IHn1. simpl. easy.
  Qed.

  (** width dl is zero imply it is a dnil *)
  Lemma dlist_w0_eq_dnil : forall (dl : dlist A), 
      width dl 0 -> dl == dnil (length dl).
  Proof.
    unfold width; induction dl; simpl; auto.
    intros. inv H. f_equiv; auto. apply length_zero_iff_nil; auto.
  Qed.

  (** rev a dnil is itself *)
  Lemma dnil_rev : forall n, rev (dnil n) == dnil n.
  Proof.
    induction n; simpl; auto. rewrite IHn. clear IHn.
    induction n; simpl; auto.
  Qed.

End dnil.


(* ===================================================================== *)
(** ** map2 for dlist *)
Section dlist_map2.
  Context `{EqEquivA:Equivalence A Aeq}.
  Context `{EqEquivB:Equivalence B Beq}.
  Context `{EqEquivC:Equivalence C Ceq}.
  Infix "=A=" := Aeq : A_scope.
  Infix "=C=" := Ceq : A_scope.
  Infix "=C=" := (eqlistA (eqlistA Ceq)).

  (** map2 dnil dl = dnil *)
  Lemma map2_dnil_l : forall dl n (f : A -> B -> C),
      length dl = n -> map2 (map2 f) (dnil n) dl =C= dnil n.
  Proof.
    intros dl n. revert dl. induction n; intros; simpl; try easy.
    destruct dl. inversion H. inversion H. rewrite H1. auto.
  Qed.

  (** map2 dl dnil = dnil *)
  Lemma map2_dnil_r : forall dl n (f : A -> B -> C),
      length dl = n -> map2 (map2 f) dl (dnil n) =C= dnil n.
  Proof.
    intros dl n. revert dl. induction n; intros; simpl; try easy.
    - rewrite map2_nil_r. easy.
    - destruct dl. easy. simpl. rewrite IHn; auto. rewrite map2_nil_r. easy.
  Qed.

  (** (map2 (map2 f) d1 d2)[i,j] = f (d1[i,j]) (d2[i,j]) *)
  Lemma nth_nth_map2_map2_rw : forall (f : A -> A -> A) (d1 d2 : dlist A) r c i j l a,
      length d1 = r -> width d1 c -> length d2 = r -> width d2 c ->
      i < r -> j < c ->
      nth j (nth i (map2 (map2 f) d1 d2) l) a =A=
        f (nth j (nth i d1 l) a) (nth j (nth i d2 l) a).
  Proof.
    intros.
    rewrite nth_map2 with (n:=r); auto.
    rewrite nth_map2 with (n:=c); auto. easy.
    apply dlist_nth_length; auto; try lia.
    apply dlist_nth_length; auto; try lia.
  Qed.

  (** (map (map f) d)[i,j] = f (d[i,j]) *)
  Lemma nth_nth_map_map : forall (d : dlist A) (f : A -> A) r c i j l a,
      length d = r -> width d c ->
      i < r -> j < c ->
      nth j (nth i (map (map f) d) l) a =A= f (nth j (nth i d l) a).
  Proof.
    intros d f r. revert d f. induction r.
    - intros. lia.
    - intros. destruct d as [|dh dt]; simpl in *. lia.
      inversion H. inversion H0. destruct i.
      + apply nth_map with (n:=c); auto.
      + apply IHr with (c:=c); auto. inv H0; auto. lia.
  Qed.
  
End dlist_map2.


(* ===================================================================== *)
(** ** Convert between dlist and function *)
Section f2dl_dl2f.
  Context `{Aequiv : Equivalence A Aeq} {Azero : A}.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  Definition f2dl (r c : nat) (f : nat -> nat -> A) : dlist A :=
    map (fun i => f2l c (f i)) (seq 0 r).

  Definition dl2f (r c : nat) (dl : dlist A) : nat -> nat -> A :=
    fun i j => nth j (nth i dl []) Azero.

  Lemma f2dl_length : forall r c f, length (f2dl r c f) = r.
  Proof.
    intros. unfold f2dl. rewrite map_length. apply seq_length.
  Qed.

  Lemma f2dl_width : forall r c f, width (f2dl r c f) c.
  Proof.
    unfold f2dl,width.
    induction r; intros; simpl; try constructor.
    - apply f2l_length.
    - rewrite <- seq_shift. rewrite List.map_map. apply IHr.
  Qed.

  (** (f2dl f)[i,j] = f i j *)
  Lemma nth_f2dl : forall {r c} f l a i j,
      i < r -> j < c -> (nth j (nth i (f2dl r c f) l) a == f i j)%A.
  Proof.
    intros. unfold f2dl. rewrite nth_map_seq; auto. rewrite nth_f2l; auto.
    f_equiv. lia.
  Qed.

End f2dl_dl2f.

Section test.
  (** [[1;2;3];[4;5;6];[7;8;9]] *)
  Let f := fun i j => i * 3 + j + 1.
  Let dl := f2dl 3 3 f.
  (* Compute dl. *)

  Let g := @dl2f _ 0 3 3 dl.
  (* Compute (g 0 0, g 0 1, g 0 2, g 1 0, g 1 1, g 1 2, g 2 0, g 2 1, g 2 2). *)
End test.  


(* ===================================================================== *)
(** ** Convert between row and col. eg, [1;2;3] <-> [[1];[2];[3]] *)
Section convert_row_and_col.
  Context `{Aequiv : Equivalence A Aeq} {Azero : A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  
  (** Convert a list to a dlist, it looks like converting a row to a column. *)
  Fixpoint row2col (l : list A) : dlist A :=
    match l with
    | [] => []
    | x :: tl => [x] :: (row2col tl)
    end.
  
  (** row2col length law *)
  Lemma row2col_length : forall l, length (row2col l) = length l.
  Proof. induction l; simpl; intros; auto. Qed.
  
  (** row2col width law *)
  Lemma row2col_width : forall l, width (row2col l) 1.
  Proof. unfold width; induction l; simpl; intros; auto. Qed.

  Lemma nth_row2col : forall l i,
      i < length l ->
      (nth i (row2col l) [] == [nth i l Azero])%list.
  Proof.
    induction l; intros; simpl in *. lia.
    destruct i; try easy. apply IHl. lia.
  Qed.
  
  (** Convert a dlist to a list which contain head element, it looks like 
      converting a column to a row. *)
  Fixpoint col2row (dl : dlist A) : list A :=
    match dl with
    | [] => []
    | l :: tl => (hd Azero l) :: (col2row tl)
    end.
  
  (** Convert a dlist to list then convert it to a dlist, equal to original dlist. *)
  Lemma row2col_col2row : forall (dl : dlist A),
      width dl 1 -> row2col (col2row dl) == dl.
  Proof.
    unfold width; induction dl; simpl; auto; intros. inv H. f_equiv; auto.
    destruct a; simpl in *; try easy. inv H2.
    eapply length_zero_iff_nil in H0. rewrite H0. easy.
  Qed.
  
  (** Convert a list to dlist then convert it to a list, equal to original list. *)
  Lemma col2row_row2col : forall (l : list A), (col2row (row2col l) == l)%list.
  Proof. induction l; simpl; auto; intros. rewrite IHl. easy. Qed.
  
End convert_row_and_col.


(* ===================================================================== *)
(** ** head column of a dlist *)
Section hdc.
  Context {A : Type} (Azero : A).
  
  (** Get head column of a dlist *)
  Fixpoint hdc (dl : dlist A) : list A :=
    match dl with
    | [] => []
    | l :: tl => (hd Azero l) :: (hdc tl)
    end.
  
  (** hdc length law *)
  Lemma hdc_length : forall dl, length (hdc dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
End hdc.


(* ===================================================================== *)
(** ** tail columns of a dlist *)
Section tlc.
  
  Context {A : Type}.
  
  (** Get tail columns of a dlist *)
  Fixpoint tlc (dl : dlist A) : dlist A :=
    match dl with
    | [] => []
    | l :: tl => (tail l) :: (tlc tl)
    end.
  
  (** tlc length law *)
  Lemma tlc_length : forall dl, length (tlc dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
  (** tlc width law when width equal to 0 *)
  Lemma tlc_width0 : forall dl, width dl 0 -> width (tlc dl) 0.
  Proof.
    unfold width; induction dl; simpl; auto. intros. inv H; constructor; auto.
    eapply List.length_zero_iff_nil in H2. subst. auto.
  Qed.
  
  (** tlc width law when width not equal to 0 *)
  Lemma tlc_widthS : forall dl c, width dl (S c) -> width (tlc dl) c.
  Proof.
    unfold width; induction dl; simpl; auto.
    intros. inv H; constructor; auto.
    destruct a; auto. easy.
  Qed.
  
End tlc.


(* ===================================================================== *)
(** ** construct a dlist with a list and a dlist by column *)
Section consc.
  Context `{Aequiv : Equivalence A Aeq} {Azero:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  
  (** Construct a dlist by column with a list and a dlist *)
  Fixpoint consc (l : list A) (dl : dlist A) : dlist A :=
    match l, dl with
    | xl :: tl, xdl :: tdl => (xl :: xdl) :: (consc tl tdl)
    | _, _ => []
    end.
  
  (** consc is injective *)
  Lemma consc_inj : forall (l1 l2 : list A) (dl1 dl2 : dlist A) n,
      length l1 = n -> length l2 = n -> length dl1 = n -> length dl2 = n ->
      consc l1 dl1 == consc l2 dl2 -> (l1 == l2)%list /\ dl1 == dl2.
  Proof.
    induction l1.
    - intros. simpl in *. subst. apply List.length_zero_iff_nil in H0,H1,H2.
      subst. easy.
    - intros. destruct l2,dl1,dl2; simpl in *; subst; try easy.
      inv H3. inv H6. eapply IHl1 in H8; auto. inv H8. split; auto.
  Qed.
  
  (** consc length law *)
  Lemma consc_length : forall l dl r,
      length l = r -> length dl = r ->
      length (consc l dl) = r.
  Proof.
    induction l,dl; simpl; intros; auto. destruct r. inversion H. f_equal.
    inversion H. inversion H0. subst. apply IHl; auto.
  Qed.
  
  (** consc width law *)
  Lemma consc_width : forall l dl c,
      length l = length dl -> width dl c ->
      width (consc l dl) (S c).
  Proof.
    unfold width; induction l,dl; simpl; intros; auto.
    inv H. inv H0. constructor; auto.
  Qed.

  (** width dl c -> length ((l @@ dl)[i]) = c + 1 *)
  Lemma nth_consc_length : forall (l : list A) dl l0 i r c,
      length l = r -> length dl = r -> width dl c -> i < r ->
      length (nth i (consc l dl) l0) = S c.
  Proof.
    intros l dl l0 i r. revert l dl l0 i. induction r; intros. lia.
    destruct l, dl; simpl in *; try lia. inversion H1. destruct i. 
    - simpl; auto.
    - apply IHr; auto. lia.
  Qed.
  
  (** consc with hdc and tlc of a dnil generate lzero *)
  Lemma consc_hdc_tlc_width0 : forall dl r, 
      length dl = r -> width dl 0 -> 
      consc (hdc Azero dl) (tlc dl) == row2col (repeat Azero r).
  Proof.
    unfold width; induction dl; simpl; intros; subst; try easy.
    inv H0. apply List.length_zero_iff_nil in H2. subst. simpl. f_equiv.
    apply IHdl; auto.
  Qed.
  
  (** consc with hdc and tlc of a dlist generate itself *)
  Lemma consc_hdc_tlc_widthS : forall dl c, 
      width dl (S c) ->
      consc (hdc Azero dl) (tlc dl) == dl.
  Proof.
    unfold width; induction dl; simpl; intros; auto. inv H. f_equiv; auto.
    - destruct a; simpl in *; try easy.
    - apply IHdl with (c:=c). auto.
  Qed.

  (** consc decompose.
    x1::l1 ++ l2::dl2 = (x::l2) :: (l1 ++ dl2)  *)
  Lemma consc_decompose : forall x1 l1 l2 dl2,
      consc (x1::l1) (l2::dl2) == (x1::l2) :: (consc l1 dl2).
  Proof. intros. simpl. easy. Qed.
  
  (** repeat (x :: l) decomposition *)
  Lemma repeat_consc : forall l x n,
      repeat (x :: l) n == consc (repeat x n) (repeat l n).
  Proof. induction n; simpl; auto. rewrite IHn. easy. Qed.

  (** Simplify consc and nthj0 *)
  Lemma consc_nthj0 : forall l dl l0 a r i,
      length l = r -> length dl = r -> i < r ->
      (nth 0 (nth i (consc l dl) l0) a == nth i l a)%A.
  Proof.
    induction l,dl; intros; simpl in *; try lia.
    destruct i; simpl; try easy. eapply IHl; auto; try lia.
  Qed.
  
  (** Simplify consc and nthSj *)
  Lemma consc_nthSj : forall l dl l0 a r c i j,
      length l = r -> length dl = r -> i < r -> j < c ->
      (nth (S j) (nth i (consc l dl) l0) a == nth j (nth i dl l0) a)%A.
  Proof.
    induction l,dl; intros; simpl in *; try lia.
    destruct i; simpl; try easy. eapply IHl; auto; try lia.
  Qed.

  (** If width dl is 0, then consc l dl = row2col l *)
  Lemma consc_dl_w0 : forall (l : list A) (dl : dlist A),
      length l = length dl ->
      width dl 0 -> (consc l dl == row2col l).
  Proof.
    induction l; intros; simpl in *. easy.
    destruct dl; simpl in *; try lia. inv H. inv H0.
    apply List.length_zero_iff_nil in H3. rewrite H3. f_equiv; auto.
  Qed.

End consc.


(* ===================================================================== *)
(** ** nth column of a dlist *)
Section nthc.
  Context `{Aequiv : Equivalence A Aeq} {Azero:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  (** Get nth column of a dlist. *)
  Fixpoint nthc (dl : dlist A) (j : nat) : list A :=
    match dl with
    | [] => []
    | l :: tl => (nth j l Azero) :: (nthc tl j)
    end.
  
  Fixpoint nthc_error (dl : dlist A) (j : nat) : option (list A) :=
    match dl with
    | [] => Some []
    | l :: tl =>
        match nth_error l j, nthc_error tl j with
        | Some a, Some l' => Some (a :: l')
        | _, _ => None
        end
    end.
  
  (** nthc length law *)
  Lemma nthc_length : forall dl j, length (nthc dl j) = length dl.
  Proof. induction dl; simpl; auto. Qed.

  (* nthc_error when overflow *)
  Lemma nthc_error_overflow_case1 : forall dl c j,
      length dl > 0 -> width dl c -> j >= c -> nthc_error dl j = None.
  Proof.
    unfold width. induction dl; intros; simpl.
    - simpl in *. lia.
    - Abort.
  
  Lemma nthc_error_overflow_case2 : forall dl c j,
      ~width dl c -> nthc_error dl j = None.
  Proof.
    unfold width.
    induction dl; intros; simpl.
    - destruct H. constructor.
    - rewrite Forall_cons_iff in H. apply not_and_or in H. destruct H.
      Abort.
    
  (* nthc_error is equal to nthc *)
  Lemma nthc_error_valid : forall dl c j,
      width dl c -> j < c ->
      Some (nthc dl j) = nthc_error dl j.
  Proof.
    induction dl; intros; simpl; auto.
    Abort.

  (** nthc_error length law *)
  Lemma nthc_error_length : forall dl c j,
      width dl c -> j < c ->
      exists l, nthc_error dl j = Some l /\ length l = length dl.
  Proof.
    induction dl; intros; simpl.
    - exists []. auto.
    - Abort.

End nthc.

Arguments nthc {A}.


(* ===================================================================== *)
(** ** Append two objects of dlist type to one object of dlist *)
Section dlapp.
  
  Context {A : Type}.
  
  (** dlist append by row *)
  Definition dlappr := app.
  
  (** dlist apend by column *)
  Fixpoint dlappc (dl1 dl2 : dlist A) : dlist A :=
    match dl1, dl2 with
    | l1 :: tl1, l2 :: tl2 => (app l1 l2) :: (dlappc tl1 tl2)
    | _, _ => []
    end.

  (** Length of dlappc is same as input *)
  Lemma dlappc_length : forall (dl1 dl2 : dlist A) r,
      length dl1 = r -> length dl2 = r -> length (dlappc dl1 dl2) = r.
  Proof.
    induction dl1, dl2; intros; simpl in *; auto.
    destruct r. lia. f_equal. apply IHdl1. lia. lia.
  Qed.

  (** Width of dlappc is the sum of each columns *)
  Lemma dlappc_width : forall (dl1 dl2 : dlist A) c1 c2,
      width dl1 c1 -> width dl2 c2 -> width (dlappc dl1 dl2) (c1 + c2).
  Proof.
    induction dl1, dl2; intros; simpl in *; auto.
    constructor. constructor. constructor.
    unfold width in *.
    constructor.
    - inv H. inv H0. apply app_length.
    - apply IHdl1. inv H; auto. inv H0; auto.
  Qed.

End dlapp.

Notation "l @@ r" := (dlappc l r) (at level 40) : dlist_scope.


(* ===================================================================== *)
(** ** Zero dlist *)
Section dlzero.
  Context `{Aequiv : Equivalence A Aeq} {Azero:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  
  (** dlist constructed by repeated lzero, named as dlzero *)
  Definition dlzero r c := repeat (lzero Azero c) r.

  (** dlzero rewrite *)
  Lemma dlzero_rw : forall r c, repeat (lzero Azero c) r = dlzero r c.
  Proof. easy. Qed.
  
  (** dlzero with S r rows could be splited to two parts *)
  Lemma dlzero_Sr : forall {r c}, dlzero (S r) c == (lzero Azero c) :: (dlzero r c).
  Proof. intros. simpl. cbn. easy. Qed.
  
  (** dlzero with 0 columns equal to dnil *)
  Lemma dlzero_c0 : forall {c}, dlzero c 0 == dnil c.
  Proof. induction c; simpl; try easy. rewrite <- IHc. easy. Qed.
  
  (** dlzero height law *)
  Lemma dlzero_length : forall {r c}, length (dlzero r c) = r.
  Proof. intros. apply repeat_length. Qed.
  
  (** dlzero width law *)
  Lemma dlzero_width : forall {r c}, width (dlzero r c) c.
  Proof.
    unfold width, dlzero; induction r; intros; simpl; auto. constructor; auto.
    apply lzero_length.
  Qed.

  (** dlzero[i] == lzero *)
  Lemma nth_dlzero : forall r c i,
      i < r -> (nth i (dlzero r c) [] == lzero Azero c)%list.
  Proof. intros. unfold dlzero. rewrite nth_repeat_inRange; auto. easy. Qed.
  
  (** append two dlzeros by row equal to whole *)
  Lemma dlzero_app_row : forall r1 r2 c,
      dlzero r1 c ++ dlzero r2 c == dlzero (r1 + r2) c.
  Proof. unfold dlzero. intros. rewrite repeat_app. easy. Qed.
  
  (** append two dlzeros by column equal to whole *)
  Lemma dlzero_app_col : forall r c1 c2,
      (dlzero r c1) @@ (dlzero r c2) == dlzero r (c1 + c2).
  Proof.
    induction r; intros; simpl; try easy. unfold dlzero,lzero in *.
    rewrite IHr. simpl. rewrite repeat_app. easy.
  Qed.

End dlzero.

Arguments dlzero {A}.


(* ===================================================================== *)
(** ** transpose a dlist *)
Section dltrans.
  Context `{Aequiv : Equivalence A Aeq} {Azero:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  
  (** Transposition of a dlist *)
  (* Idea: fetch row as column one bye one, generate a dlist with c rows if 
      given c is <= column of input dlist.

      Note that, we give c to support dlist_0_c situation.
      eg: 
      [] 3 => [[];[];[]]
      [[];[];[]] 0 => []
   *)
  Fixpoint dltrans (dl : dlist A) (c : nat) : dlist A :=
    match dl with
    | [] => @dnil A c
    | l :: tl => consc l (dltrans tl c)
    end.

  #[export] Instance dltrans_wd :
    Proper (eqlistA (eqlistA Aeq) ==> eq ==> eqlistA (eqlistA Aeq)) dltrans.
  Proof.
    simp_proper. induction x; intros.
    - destruct y; subst; easy.
    - destruct y. easy. inv H. simpl. rewrite H4. rewrite (IHx y); easy.
  Qed.
  
  (** dltrans length law *)
  Lemma dltrans_length : forall dl c, width dl c -> length (dltrans dl c) = c.
  Proof.
    induction dl; intros; simpl; auto.
    - rewrite dnil_length. auto.
    - inversion H. rewrite consc_length with (r:=c); auto.
  Qed.
  
  (** dltrans width law *)
  Lemma dltrans_width : forall dl r c, 
      length dl = r -> width dl c -> width (dltrans dl c) r.
  Proof.
    unfold width; induction dl; intros; simpl in *; auto.
    - induction c; simpl in *; auto.
    - rewrite <- H. inv H0. apply consc_width.
      + rewrite dltrans_length; auto.
      + apply IHdl; auto. 
  Qed.
  
  (** dltrans dnil = [] *)
  Lemma dltrans_nil : forall n, dltrans (dnil n) 0 == [].
  Proof.
    intros. destruct n; simpl. reflexivity. easy.
  Qed.
  
  (** dltrans consr = consc dltrans *)
  Lemma dltrans_consr : forall dl l c,
      dltrans (l :: dl) c == consc l (dltrans dl c).
  Proof.
    intros. simpl. easy.
  Qed.
  
  (** dltrans consc = consr dltrans *)
  Lemma dltrans_consc : forall dl l r c,
      length l = r -> length dl = r -> width dl c ->
      dltrans (consc l dl) (S c) == l :: (dltrans dl c).
  Proof.
    unfold width; induction dl; simpl; intros; subst.
    - destruct l; simpl; try easy.
    - destruct l. easy.
      inv H0. inv H1.
      specialize (IHdl l (length l) (length a) eq_refl H2 H4).
      simpl.
      destruct (dltrans (consc l dl) (S (length a))). easy.
      inv IHdl. rewrite H3, <- H6. easy.
  Qed.
  
  (** dltrans twice return back *)
  Lemma dltrans_dltrans : forall dl r c,
      length dl = r -> width dl c -> dltrans (dltrans dl c) r == dl.
  Proof.
    induction dl; intros; simpl in *.
    - subst. destruct c; simpl; auto.
    - destruct r. easy. inv H. inv H0.
      unfold width in *.
      rewrite dltrans_consc with (r:=length a);
        auto using dltrans_length, dltrans_width.
      f_equiv. auto.
  Qed.
  
  (** dltrans dlzero<r,c> = dlzero<c,r> *)
  Lemma dltrans_zero : forall r c,
      dltrans (dlzero Azero r c ) c == dlzero Azero c r.
  Proof.
    induction r; intros; simpl; auto. rewrite dlzero_c0; easy.
    unfold dlzero in *; simpl in *. rewrite IHr.
    rewrite repeat_consc. easy.
  Qed.

  (** (dltrans dl)[i,j] = dl[j,i] *)
  Lemma dltrans_ij : forall (dl : dlist A) r c a i j,
      length dl = r -> width dl c ->
      i < r -> j < c ->
      (nth i (nth j (dltrans dl c) []) a == nth j (nth i dl []) a)%A.
  Proof.
    induction dl; intros; simpl in *.
    - subst. lia.
    - destruct r. lia. inversion H. inversion H0. destruct i.
      + erewrite consc_nthj0; try easy. rewrite dltrans_length; auto. lia.
      + erewrite consc_nthSj; auto. eapply IHdl; auto. lia.
        rewrite dltrans_length; auto. lia.
  Qed.
  
  (** (dltrans dl)[i,i] = dl[i,i] *)
  Lemma nth_dltrans_ii : forall (dl : dlist A) n a i,
      length dl = n -> width dl n ->
      (nth i (nth i (dltrans dl n) []) a == nth i (nth i dl []) a)%A.
  Proof.
    intros.
    destruct (i <? n) eqn:i_lt_n.
    - apply Nat.ltb_lt in i_lt_n. erewrite dltrans_ij; try easy. lia.
    - apply Nat.ltb_ge in i_lt_n.
      repeat rewrite !nth_overflow; simpl in *; try easy; try lia.
      rewrite dltrans_length; auto.
  Qed.
  
  (* (** (fun i => (dltrans dl)[i,i]) = (fun i => dl[i,i]) *) *)
  (* Lemma dltrans_ii_fun : forall (dl : dlist A) n a, *)
  (*     length dl = n -> width dl n -> *)
  (*     (fun i : nat => nth i (nth i (dltrans dl n) []) a) =
         (fun i => nth i (nth i dl []) a). *)
  (* Proof. *)
  (*   intros. apply functional_extensionality. *)
  (*   intros. apply dltrans_ii; auto. *)
  (* Qed. *)
  
End dltrans.

Global Hint Resolve
  dltrans_length
  dltrans_width : list.


(* ===================================================================== *)
(** ** dlist unit, like a identity matrix *)
Section dlunit.
  Context `{Aequiv : Equivalence A Aeq} {Azero Aone:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  
  (** Build a identity matrix with dlist. *)
  (* there are 4 parts of a dlunit [n x n]: 
     A B
     C D,
     where, A is 1, B is a 1x(n-1) row matrix with all 0,
     C is (n-1)x1 column matrix with all 0, D is (n-1)*(n-1) identity matrix *)
  Fixpoint dlunit (n : nat) : dlist A :=
    match n with
    | O => []
    | S n0 => (1 :: (repeat 0 n0)) :: (consc (repeat 0 n0) (dlunit n0))
    end.
  
  (** dlunit length law *)
  Lemma dlunit_length : forall {n}, length (dlunit n) = n.
  Proof.
    induction n; simpl; auto. f_equal.
    rewrite consc_length with (r:=n); auto. apply repeat_length.
  Qed.
  
  (** dlunit width law *)
  Lemma dlunit_width : forall {n}, width (dlunit n) n.
  Proof.
    unfold width; induction n; simpl; auto. constructor.
    - simpl. f_equal. apply repeat_length.
    - apply consc_width; auto. rewrite repeat_length, dlunit_length; auto.
  Qed.

  Hint Resolve dlunit_length dlunit_width : list.
  
  (** length(dlunit[i]) = n  *)
  Lemma nth_dlunit_length : forall n i l,
      i < n -> length (nth i (dlunit n) l) = n.
  Proof.
    induction n; intros. lia. simpl. destruct i.
    - simpl. rewrite repeat_length. auto.
    - rewrite nth_consc_length with (r:=n)(c:=n); auto with list. lia.
  Qed.

  (** (dlunit)[i,i] == 1 *)
  Lemma dlunit_ii : forall n i l a, i < n -> (nth i (nth i (dlunit n) l) a == 1)%A.
  Proof.
    induction n; intros. lia. destruct i; simpl. easy.
    rewrite consc_nthSj with (r:=n) (c:=n); try lia; auto with list.
    apply IHn. lia.
  Qed.
    
  (** i<>j -> (dlunit)[i,j] == 0 *)
  Lemma dlunit_ij : forall n i j l a,
      i < n -> j < n -> i <> j -> (nth j (nth i (dlunit n) l) a == 0)%A.
  Proof.
    induction n; intros. lia. destruct i,j; simpl; auto; try lia.
    - apply nth_repeat_inRange. lia.
    - rewrite consc_nthj0 with (r:=n); auto with list; try lia.
      apply nth_repeat_inRange; lia.
    - rewrite consc_nthSj with (r:=n)(c:=n); auto with list; try lia.
      apply IHn; lia.
  Qed.
  
  (** transpose dlunit keep unchanged *)
  Lemma dltrans_dlunit : forall {n}, dltrans (dlunit n) n == (dlunit n).
  Proof.
    induction n; simpl; try easy.
    assert ((dltrans (consc (repeat 0 n) (dlunit n)) (S n)) ==
              (repeat 0 n) :: (dltrans (dlunit n) n)).
    { apply dltrans_consc with (r:=n).
      apply repeat_length. apply dlunit_length. apply dlunit_width. }
    destruct (dltrans (consc (repeat 0 n) (dlunit n)) (S n)). easy.
    inv H. f_equiv. f_equiv; auto. f_equiv. rewrite H5. auto.
  Qed.

End dlunit.

Arguments dlunit {A}.

Hint Resolve
  dlunit_length dlunit_width
  : list.


(* ===================================================================== *)
(** ** map of dlist with f : A -> B *)

Section dmap.
  Context `{Aequiv : Equivalence A Aeq}.
  Context `{Bequiv : Equivalence B Beq}.
  Variable f : A -> B.
  Context {f_wd : Proper (Aeq ==> Beq) f}.
  Infix "==" := Beq : A_scope.
  Infix "==" := (eqlistA Beq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Beq)).
  
  (** map operation to dlist *)
  Definition dmap dl := map (map f) dl.

  (** dmap length law *)
  Lemma dmap_length : forall dl, length (dmap dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
  (** dmap width law *)
  Lemma dmap_width : forall dl n,  width dl n <-> width (dmap dl) n.
  Proof.
    unfold width; induction dl; intros; split; intros; simpl in *; try easy.
    - inv H. constructor. apply map_length. apply IHdl. auto.
    - inv H. constructor. rewrite map_length. auto.
      apply IHdl. auto.
  Qed.
  
  (** dmap effect equal to map to first head and dmap to tail rows *) 
  Lemma dmap_cons : forall l dl, dmap (l :: dl) == (map f l) :: (dmap dl).
  Proof. intros. simpl. easy. Qed.
  
  (** dmap distributive law by append *)
  Lemma dmap_app : forall dl1 dl2, dmap (dl1 ++ dl2) == (dmap dl1) ++ (dmap dl2).
  Proof.
    induction dl1; destruct dl2; simpl in *; rewrite ?app_nil_r; try easy.
    rewrite IHdl1. easy.
  Qed.
  
  (** dmap dnil = dnil *)
  Lemma dmap_dnil : forall n, dmap (dnil n) == dnil n.
  Proof. induction n; simpl; try easy. rewrite IHn. easy. Qed.

  (** (map f l) @@ (dmap f dl) == dmap f (l @@ dl)  *)
  Lemma consc_map_dmap : forall l dl, consc (map f l) (dmap dl) == dmap (consc l dl).
  Proof.
    induction l; intros; simpl; auto.
    destruct dl; simpl; auto. rewrite IHl. easy.
  Qed.
  
  (** dltrans and dmap *)
  Lemma dltrans_dmap : forall dl c,
      width dl c -> dltrans (dmap dl) c == dmap (dltrans dl c).
  Proof.
    induction dl; intros; simpl in *. rewrite dmap_dnil; try easy.
    inversion H. rewrite IHdl; auto. apply consc_map_dmap.
  Qed.
  
End dmap.

Hint Unfold dmap : list.

(** Properties for dmap over two types *)
Section dmap_A_B.
  Context {A:Type} `{Bequiv : Equivalence B Beq}.
  Infix "==" := Beq : A_scope.
  Infix "==" := (eqlistA (eqlistA Beq)) : dlist_scope.

  (** dmap extensional law  *)
  Lemma dmap_ext : forall dl (f g : A -> B) (H : forall a, (f a == g a)%A),
      (dmap f dl == dmap g dl)%dlist.
  Proof.
    intros. unfold dmap.
    apply map_ext. intros. induction a; simpl; auto.
  Qed.
  
End dmap_A_B.

(** Properties for dmap over three types *)
Section dmap_A_B_C.
  Context `{Aequiv:Equivalence A Aeq}.
  Context `{Bequiv:Equivalence B Beq}.
  Context `{Cequiv:Equivalence C Ceq}.
  Infix "==" := (eqlistA (eqlistA Ceq)) : dlist_scope.
  (* Context {A B C: Type}. *)

  (** dmap f (dmap g dl) = dmap (f . g) dl  *)
  Lemma dmap_dmap : forall dl (f : A -> B) (g : B -> C),
      dmap g (dmap f dl) == dmap (fun x => g (f x)) dl.
  Proof. induction dl; intros; simpl. easy. f_equiv; auto. apply map_map. Qed.
  
End dmap_A_B_C.

(** Properties for dmap over one type *)
Section dmap_A_A.
  Context `{Aequiv : Equivalence A Aeq} {Azero:A}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)).

  (** dmap (fun x => Azero) dl = dlzero Azero r c *)
  Lemma dmap_eq_zero : forall {r c} dl,
      length dl = r -> width dl c ->
      dmap (fun (x : A) => Azero) dl == dlzero Azero r c.
  Proof.
    intros. unfold dmap,dlzero.
    
    (* Note that, use "map_eq_zero" cannot prove this lemma.
       Although this method looks very simple. *)
    (* apply map_eq_zero; auto. intros. apply map_eq_zero; try easy. *)
    
    revert r c H H0.
    induction dl; intros; simpl in *.
    - subst. easy.
    - destruct r; try easy. inv H. inv H0. simpl. f_equiv.
      + apply map_eq_zero; auto. easy.
      + apply IHdl; auto.
  Qed.

End dmap_A_A.


(* ===================================================================== *)
(** ** map2 of dlist *)
Section dmap2.
  Context {A B : Type} `{Equiv_Ceq:Equivalence C Ceq}.
  Variable f : A -> B -> C.
  Infix "==" := (eqlistA (eqlistA Ceq)).
  
  (** map operation to two dlists *)
  Definition dmap2 dl1 dl2 := map2 (map2 f) dl1 dl2.
  
  (** dmap2 length law *)
  Lemma dmap2_length : forall dl1 dl2,
      length dl1 = length dl2 -> length (dmap2 dl1 dl2) = length dl1.
  Proof.
    induction dl1,dl2; simpl; auto.
  Qed.
  
  (** dmap2 width law *)
  Lemma dmap2_width : forall dl1 dl2 n,
      width dl1 n -> width dl2 n -> width (dmap2 dl1 dl2) n.
  Proof. 
    unfold width; induction dl1; intros; simpl in *; auto.
    destruct dl2; auto. inv H. inv H0. constructor.
    apply map2_length; auto. apply IHdl1; auto.
  Qed.
  
  (** dmap2 and consr *)
  Lemma dmap2_consr : forall dl1 dl2 l1 l2,
      dmap2 (l1 :: dl1) (l2 :: dl2) == (map2 f l1 l2) :: (dmap2 dl1 dl2).
  Proof. intros. simpl. easy. Qed.
  
  (** dmap2 and consc *)
  Lemma dmap2_consc : forall l1 dl1 l2 dl2 c,
      length l1 = length dl1 ->
      length l2 = length dl2 ->
      width dl1 c -> width dl2 c ->
      dmap2 (consc l1 dl1) (consc l2 dl2) == consc (map2 f l1 l2) (dmap2 dl1 dl2).
  Proof.
    unfold width; induction l1,dl1,l2,dl2; simpl; intros; try easy.
    (* destruct r,t; try easy. *)
    inv H1. inv H2.
    f_equiv. apply IHl1 with (c:=length l); auto.
  Qed.
  
  (** dmap2 and app *)
  Lemma dmap2_app : forall dla1 dla2 dlb1 dlb2,
      length dla1 = length dlb1 ->
      length dla2 = length dlb2 ->
      dmap2 (dla1 ++ dla2) (dlb1 ++ dlb2) ==
        (dmap2 dla1 dlb1) ++ (dmap2 dla2 dlb2).
  Proof. intros. unfold dmap2. apply map2_app; auto. Qed.
  
  (** dmap2 dnil dl == dnil *)
  Lemma dmap2_dnil_l : forall dl n, length dl = n -> dmap2 (dnil n) dl == dnil n.
  Proof. intros. unfold dmap2. rewrite map2_dnil_l; easy. Qed.

  (** dmap2 dl dnil = dnil *)
  Lemma dmap2_dnil_r : forall dl n, length dl = n -> dmap2 dl (dnil n) == dnil n.
  Proof. intros. unfold dmap2. rewrite map2_dnil_r; easy. Qed.

  Lemma tl_dmap2 : forall dl1 dl2,
      length dl1 = length dl2 -> tl (dmap2 dl1 dl2) == dmap2 (tl dl1) (tl dl2).
  Proof. intros. unfold dmap2. apply tail_map2_dlist. Qed.

  (** dltrans and dmap2 *)
  Lemma dltrans_dmap2 : forall dl1 dl2 c,
      length dl1 = length dl2 ->
      width dl1 c -> width dl2 c ->
      dltrans (dmap2 dl1 dl2) c == dmap2 (dltrans dl1 c) (dltrans dl2 c).
  Proof.
    unfold width; induction dl1; intros; simpl in *; subst.
    rewrite dmap2_dnil_l; auto using dltrans_length. easy.
    destruct dl2; simpl in *. easy.
    inv H. inv H0. inv H1. rewrite IHdl1; auto.
    erewrite dmap2_consc; auto using dltrans_width, dltrans_length; try easy.
    rewrite dltrans_length; auto. rewrite dltrans_length; auto.
  Qed.
  
End dmap2.

(** Properties of dmap2 on one type *)
Section dmap2_A.
  Context `{HAMonoid : AMonoid}.
  Infix "+" := Aadd : A_scope.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  (** (dl1 . dl2) . dl3 = dl1 . (dl2 . dl3) *)
  Lemma dmap2_assoc : forall (dl1 dl2 dl3 : dlist A),
      dmap2 Aadd (dmap2 Aadd dl1 dl2) dl3 == dmap2 Aadd dl1 (dmap2 Aadd dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; auto. f_equiv; auto. apply map2_assoc.
  Qed.
  
  (** dl1 . dl2 == dl2 . dl1 *)
  Lemma dmap2_comm : forall (dl1 dl2 : dlist A), dmap2 Aadd dl1 dl2 == dmap2 Aadd dl2 dl1.
  Proof. induction dl1,dl2; simpl; auto. f_equiv; auto. apply map2_comm. Qed.
  
  (** dmap2 with dmap of two components *)
  Lemma dmap2_dmap_dmap :
    forall (f1 f2 g : A -> A) (h : A -> A -> A) 
      (H : forall x, (g x == h (f1 x) (f2 x))%A) l,
      dmap2 h (dmap f1 l) (dmap f2 l) == dmap g l.
  Proof.
    induction l; simpl; auto. rewrite IHl. f_equiv; try easy.
    apply map2_map_map. easy.
  Qed.

  (** dmap2 over dmap is homorphism *)
  Lemma dmap2_dmap_hom :
    forall (Aopp : A -> A)
      (H : forall a b : A, (Aopp (a + b) == (Aopp a) + (Aopp b))%A)
      d1 d2,
      dmap2 Aadd (dmap Aopp d1) (dmap Aopp d2) == dmap Aopp (dmap2 Aadd d1 d2).
  Proof.
    intros. revert d2.
    induction d1,d2; simpl; try easy. rewrite IHd1. f_equiv.
    apply map2_map_hom. easy.
  Qed.
  
End dmap2_A.


(* ===================================================================== *)
(** ** Addition, opposition and subtraction on dlist *)
Section dladd_dlopp_dlsub.

  Context `{AG:AGroup}.
  Infix "==" := (eqlistA (eqlistA Aeq)).
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (-b)).
  Infix "-" := Asub : A_scope. 

  Notation dladd := (dmap2 Aadd).
  Notation dlopp := (dmap Aopp).
  Notation dlsub := (dmap2 Asub).
  
  (** dl + 0 = dl *)
  Lemma dladd_zero_l : forall dl r c, 
      length dl = r -> width dl c ->
      dladd (dlzero Azero r c) dl == dl.
  Proof.
    unfold width, dlzero in *. induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - destruct r. easy. inv H. inv H0. simpl. f_equiv; auto.
      rewrite map2_zero_l; auto. easy.
  Qed.
  
  (** 0 + dl = dl *)
  Lemma dladd_zero_r : forall dl r c, 
      length dl = r -> width dl c ->
      dladd dl (dlzero Azero r c) == dl.
  Proof. intros. rewrite dmap2_comm; auto. apply dladd_zero_l; auto. Qed.

  (** dl1 - dl2 = - (dl2 - dl1) *)
  Lemma dlsub_comm : forall dl1 dl2 c,
      length dl1 = length dl2 -> width dl1 c -> width dl2 c ->
      dlsub dl1 dl2 == dlopp (dlsub dl2 dl1).
  Proof.
    induction dl1,dl2; simpl; intros; auto. f_equiv.
    - rewrite map2_sub_comm. easy.
    - inv H. inv H0. inv H1.
      apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** (dl1 - dl2) - dl3 = dl1 - (dl2 + dl3) *)
  Lemma dlsub_assoc : forall dl1 dl2 dl3 c, 
      length dl1 = length dl2 -> length dl2 = length dl3 ->
      width dl1 c -> width dl2 c -> width dl3 c ->
      dlsub (dlsub dl1 dl2) dl3 == dlsub dl1 (dladd dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; intros; auto. f_equiv.
    - apply map2_sub_assoc.
    - inv H. inv H0. inv H1. inv H2. inv H3. apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** 0 - dl = - dl *)
  Lemma dlsub_zero_l : forall dl r c, 
      length dl = r -> width dl c ->
      dlsub (dlzero Azero r c) dl == dlopp dl.
  Proof.
    induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - induction r. easy. inv H. inv H0. simpl.
      unfold dlzero in *. f_equiv; auto. apply lsub_zero_l; auto.
  Qed.
  
  (** dl - 0 = dl *)
  Lemma dlsub_zero_r : forall dl r c, 
      length dl = r -> width dl c ->
      dlsub dl (dlzero Azero r c) == dl.
  Proof.
    induction dl; simpl; intros; auto. destruct r; simpl. easy.
    inv H. inv H0. f_equiv; auto.
    apply lsub_zero_r; auto. apply IHdl; auto. 
  Qed.
  
  (** dl - dl = 0 *)
  Lemma dlsub_self : forall dl r c, 
      length dl = r -> width dl c ->
      dlsub dl dl == (dlzero Azero r c).
  Proof.
    induction dl; simpl; intros; subst; try easy. inv H0.
    rewrite (IHdl (length dl) (length a)); auto.
    unfold dlzero in *. simpl. f_equiv; try easy. apply lsub_self; auto.
  Qed.

End dladd_dlopp_dlsub.


(* ===================================================================== *)
(** ** list dot dlist, and dlist dot dlist *)
Section ldotdl_dldotdl.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- b" := (Aopp b) : A_scope.
  Notation Asub := (fun a b => a + (-b)).
  Infix "-" := Asub : A_scope.
  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  
  Notation ladd := (map2 Aadd).
  Notation lopp := (map Aopp).
  Notation ldot := (@ldot _ Aadd Azero Amul).
  Notation lcmul := (fun a l => map (fun x => a * x) l).

  Notation dladd := (dmap2 Aadd).
  Notation dlopp := (dmap Aopp).
  
  (** list dot product to dlist *)
  Fixpoint ldotdl (l : list A) (dl : dlist A) : list A :=
    match dl with
    | h :: t => (ldot l h) :: (ldotdl l t)
    | [] => []
    end.

  #[export] Instance ldotdl_wd :
    Proper (eqlistA Aeq ==> eqlistA (eqlistA Aeq) ==> eqlistA Aeq) ldotdl.
  Proof.
    simp_proper.
    intros l1 l2 H dl1. revert l1 l2 H. induction dl1; simpl; intros.
    - destruct y; try easy.
    - destruct y; try easy. simpl. inv H0. apply cons_eq_iff; split; auto.
      rewrite H,H4. easy.
  Qed.
  
  (** ldotdl left with nil *)
  Lemma ldotdl_nil_l : forall dl r,
      length dl = r -> (ldotdl [] dl == lzero Azero r)%list.
  Proof.
    induction dl; simpl; intros; subst; try easy. rewrite ldot_nil_l.
    rewrite IHdl with (r:=length dl); simpl; auto. easy.
  Qed.
  
  (** ldotdl right with nil *)
  Lemma ldotdl_nil_r : forall r l, (ldotdl l (dnil r) == lzero Azero r)%list.
  Proof.
    induction r; simpl; intros; auto. rewrite IHr. rewrite ldot_nil_r. easy.
  Qed.

  (** ldotdl length law *)
  Lemma ldotdl_length : forall dl l r,
      length dl = r -> length (ldotdl l dl) = r.
  Proof.
    induction dl; intros; simpl in *; auto.
    destruct r. easy. rewrite IHdl with (r:=r); auto.
  Qed.
  
  (** (- l) * dl = - (l * dl) *)
  Lemma ldotdl_lopp : forall l dl c,
      length l = c -> width dl c -> 
      (ldotdl (lopp l) dl == lopp (ldotdl l dl))%list.
  Proof.
    induction dl; simpl; intros; auto. inv H. inv H0. f_equiv.
    - apply ldot_lopp_l with (r:=length l); auto.
    - apply IHdl with (c:=length l); auto.
  Qed.
  
  (** l * (- dl) = - (l * dl) *)
  Lemma ldotdl_dlopp : forall l dl c,
      length l = c -> width dl c -> 
      (ldotdl l (dlopp dl) == lopp (ldotdl l dl))%list.
  Proof.
    induction dl; simpl; intros; auto. inv H0. f_equiv.
    - apply ldot_lopp_r with (r:=length l); auto.
    - apply IHdl with (c:=length l); auto.
  Qed.
  
  (** l * (dl1 + dl2) = l * dl1 + l * dl2 *)
  Lemma ldotdl_dladd : forall l dl1 dl2 c,
      length l = c -> width dl1 c -> width dl2 c ->
      (ldotdl l (dladd dl1 dl2) == ladd (ldotdl l dl1) (ldotdl l dl2))%list.
  Proof.
    induction dl1,dl2; simpl; intros; auto. inv H0. inv H1. f_equiv.
    - rewrite ldot_ladd_r with (r:=length a); try easy. lia.
    - apply IHdl1 with (c:=length l); auto.
  Qed.

  (** (l1 + l2) * dl = l1 * dl + l2 * dl *)
  Lemma ldotdl_ladd : forall dl l1 l2 {c},
      length l1 = length l2 ->
      length dl = c -> width dl (length l1) ->
      (ldotdl (ladd l1 l2) dl == ladd (ldotdl l1 dl) (ldotdl l2 dl))%list.
  Proof.
    induction dl; intros; simpl; auto. inv H1. f_equiv.
    - apply ldot_ladd_l with (r:=length l1); auto.
    - apply IHdl with (c:=length dl); auto.
  Qed.
  
  (** 0 * dl = 0 *)
  Lemma ldotdl_zero_l : forall dl r c,
      length dl = r -> width dl c ->
      (ldotdl (lzero Azero c) dl == lzero Azero r)%list.
  Proof.
    induction dl; simpl; intros; auto.
    - subst; easy.
    - inv H0. rewrite IHdl with (r:=length dl); auto. rewrite ldot_zero_l; easy.
  Qed.
  
  (** l * 0 = 0 *)
  Lemma ldotdl_zero_r : forall l r c,
      length l = c -> (ldotdl l (dlzero Azero r c) == lzero Azero r)%list.
  Proof.
    induction r; simpl; intros; auto. unfold dlzero in *. rewrite IHr; auto.
    rewrite ldot_zero_r. easy.
  Qed.
  
  (** ldotdl of consr and consc *)
  Lemma ldotdl_consr_consc : forall l2 dl2 l1 x1 r c,
      length l2 = c -> length dl2 = c -> width dl2 r ->
      (ldotdl (x1 :: l1) (consc l2 dl2) == ladd (lcmul x1 l2) (ldotdl l1 dl2))%list.
  Proof.
    induction l2, dl2; simpl; intros; auto. inv H1.
    rewrite ldot_cons. f_equiv. eapply IHl2; auto. apply H5.
  Qed.

  (** ldot and ldotdl could swap first two operands.
    l1 . (l2 . dl) = l2 . (l1 . dl^T) *)
  Lemma ldot_ldotdl_swap12 : forall dl l1 l2 r c,
      length l1 = r -> length l2 = c -> length dl = r -> width dl c ->
      (ldot l1 (ldotdl l2 dl) == ldot l2 (ldotdl l1 (dltrans dl c)))%A.
  Proof.
    induction dl,l1; simpl; intros; try easy.
    - rewrite ldotdl_nil_l with (r:=c); try apply dnil_length.
      rewrite ldot_zero_r; cbv. easy.
    - subst. inversion H1.
    - subst. inversion H1.
    - inv H2. rewrite ldot_cons.
      rewrite ldotdl_consr_consc with (r:=length l1) (c:=length a); auto.
      + rewrite ldot_ladd_r with (r:=length l2);
          auto using lcmul_length, ldotdl_length, dltrans_length.
        rewrite <- IHdl with (r:=length l1); auto.
        rewrite (ldot_lcmul_r _ _ a0). easy.
      + rewrite dltrans_length; auto.
      + apply dltrans_width; auto.
  Qed.

  (** ldotdl with consr at right operend *)
  Lemma ldotdl_consr_r : forall l1 l2 dl2 r c,
      length l1 = r -> length l2 = r -> length dl2 = c -> width dl2 r ->
      (ldotdl l1 (l2 :: dl2) == (ldot l1 l2) :: (ldotdl l1 dl2))%list.
  Proof. induction l1,l2,dl2; simpl; intros; easy. Qed.
  
  (** ldotdl right distributive over ladd.
    (l1 + l2) . dl = l1 . dl + l2.dl *)
  Lemma ldotdl_ladd_distr_r : forall l1 l2 dl r c,
      length l1 = r -> length l2 = r -> length dl = c -> width dl r ->
      (ldotdl (ladd l1 l2) dl == ladd (ldotdl l1 dl) (ldotdl l2 dl))%list.
  Proof.
    induction dl; simpl; intros; auto. inv H2.
    rewrite <- IHdl with (r:=length l1) (c:=length dl); auto.
    rewrite ldot_ladd_l with (r:=length l1); easy.
  Qed.
  
  (** ldotdl with lcmul is assocociative.
    cmul a (dot l dl) = dot (cmul a l) dl *)
  Lemma ldotdl_lcmul_assoc : forall dl a l r c,
      length l = r -> length dl = c -> width dl r ->
      (lcmul a (ldotdl l dl) == ldotdl (lcmul a l) dl)%list.
  Proof.
    induction dl; simpl; intros; auto. inv H1.
    rewrite IHdl with (r:=length l) (c:=length dl); auto.
    rewrite (ldot_lcmul_l _ _ a0). easy.
  Qed.
  
  (** l dotdl E = l *)
  Lemma ldotdl_dlunit : forall l {n},
      length l = n -> (ldotdl l (dlunit 0 1 n) == l)%list.
  Proof.
    induction l; simpl; intros; auto.
    - subst. simpl. easy.
    - destruct n. easy. inv H. simpl. f_equiv.
      + rewrite ldot_cons. rewrite ldot_zero_r. ring.
      + erewrite (ldotdl_consr_consc);
          try apply repeat_length; try apply dlunit_length; try apply dlunit_width.
        rewrite IHl; try easy.
        rewrite (lcmul_zero_r a). rewrite ladd_zero_l; easy.
  Qed.


  (** dlist dot product *)
  Fixpoint dldotdl (dl1 dl2 : dlist A) : dlist A :=
    match dl1 with
    | h1 :: t1 => (ldotdl h1 dl2) :: (dldotdl t1 dl2)
    | [] => []
    end.

  #[export] Instance dldotdl_wd :
    let deq := eqlistA (eqlistA Aeq) in
    Proper (deq ==> deq ==> deq) dldotdl.
  Proof.
    simp_proper. induction x; intros.
    - destruct y; easy.
    - destruct y; try easy. simpl. inv H. apply cons_eq_iff; split; auto.
      rewrite H4,H0. easy.
  Qed.
  
  (** dldotdl length law *)
  Lemma dldotdl_length : forall dl1 dl2 r1,
      length dl1 = r1 -> length (dldotdl dl1 dl2) = r1.
  Proof.
    induction dl1; intros; auto. simpl in *. destruct r1. easy.
    rewrite IHdl1 with (r1:=r1); auto.
  Qed.

  (** dldotdl width law *)
  Lemma dldotdl_width : forall dl1 dl2 r2 c,
      length dl2 = r2 -> width dl1 c -> width dl2 c ->
      width (dldotdl dl1 dl2) r2.
  Proof.
    unfold width; induction dl1; intros; simpl in *; auto. inv H0. constructor.
    - apply ldotdl_length; auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.

  (** dldotdl consr left *)
  Lemma dldotdl_consr_l : forall l1 dl1 dl2,
      dldotdl (l1 :: dl1) dl2 == (ldotdl l1 dl2) :: (dldotdl dl1 dl2). 
  Proof. simpl. easy. Qed.
  
  (** dldotdl consr right *)
  Lemma dldotdl_consr_r : forall dl1 l2 dl2 c,
      length l2 = c ->
      width dl1 c ->
      width dl2 c ->
      dldotdl dl1 (l2 :: dl2) == consc (ldotdl l2 dl1) (dldotdl dl1 dl2).
  Proof.
    induction dl1; simpl; intros; auto. inv H0.
    rewrite ldot_comm.
    rewrite IHdl1 with (c:=length l2); auto. easy.
  Qed.

  (** (- dl1) * dl2 = - (dl1 * dl2) *)
  Lemma dldotdl_dlopp_l : forall dl1 dl2 {c},
      width dl1 c -> width dl2 c ->
      dldotdl (dlopp dl1) dl2 == dlopp (dldotdl dl1 dl2).
  Proof.
    induction dl1; simpl; intros; auto. inv H. f_equiv.
    - apply ldotdl_lopp with (c:=length a); auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.

  (** dl1 * (- dl2) = - (dl1 * dl2) *)
  Lemma dldotdl_dlopp_r : forall dl1 dl2 {c},
      width dl1 c -> width dl2 c ->
      dldotdl dl1 (dlopp dl2) == dlopp (dldotdl dl1 dl2).
  Proof.
    induction dl1; simpl; intros; auto. inv H. f_equiv.
    - apply ldotdl_dlopp with (c:=length a); auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** dl1 * (dl2 + dl3) = dl1 * dl2 + dl1 * dl3 *)
  Lemma dldotdl_dladd_l : forall dl1 dl2 dl3 {c},
      width dl1 c -> width dl2 c -> width dl3 c -> 
      dldotdl dl1 (dladd dl2 dl3) == dladd (dldotdl dl1 dl2) (dldotdl dl1 dl3).
  Proof.
    induction dl1; simpl; intros; auto. inv H. f_equiv.
    - apply ldotdl_dladd with (c:=length a); auto.
    - apply IHdl1 with (c:=length a); auto.
  Qed.
  
  (** (dl1 + dl2) * dl3 = dl1 * dl3 + dl2 * dl3 *)
  Lemma dldotdl_dladd_r : forall dl1 dl2 dl3 {c},
      width dl1 c -> width dl2 c -> width dl3 c -> 
      dldotdl (dladd dl1 dl2) dl3 == dladd (dldotdl dl1 dl3) (dldotdl dl2 dl3).
  Proof.
    induction dl1, dl2; intros; simpl in *; try easy. inv H. inv H0. f_equiv.
    - apply ldotdl_ladd with (c:=length dl3); auto.
    - apply IHdl1 with (c:=length a); auto. 
  Qed.

  (** dldotdl [] dl = [] *)
  Lemma dldotdl_nil_l : forall dl, dldotdl [] dl == [].
  Proof. intros. simpl. auto. Qed.
  
  (** dldotdl dl [] = dnil *)
  Lemma dldotdl_nil_r : forall dl, dldotdl dl [] == dnil (length dl).
  Proof. induction dl; simpl; intros; subst; simpl; subst; try easy. auto. Qed.

  Section test.
    Variable a11 a12 a21 a22 : A.
    Let d1 := [[a11;a12]].
    Let d2 := [[a11;a12];[a21;a22]].
    (* Compute dldotdl d1 d2. *)
    (* Compute dldotdl (dnil 2) d1. *)
    (* Compute dldotdl (dnil 2) d2. *)
    (* Compute dldotdl (dnil 3) d2. *)
    (* Compute dldotdl d1 (dnil 2). *)
    (* Compute dldotdl d2 (dnil 2). *)
    (* Compute dldotdl d2 (dnil 3). *)
    (* Compute ldotdl [] d2. *)
  End test.

  (** dldotdl dnil dl = dlzero *)
  Lemma dldotdl_dnil_l : forall dl n r c,
      length dl = r -> width dl c ->
      dldotdl (dnil n) dl == dlzero Azero n r.
  Proof.
    intros dl n. revert dl. induction n; intros; simpl; auto.
    rewrite dlzero_Sr. f_equiv.
    - rewrite ldotdl_nil_l with (r:=r); auto. easy.
    - apply IHn with (c:=c); auto.
  Qed.
  
  (** dldotdl dl dnil = dnil *)
  Lemma dldotdl_dnil_r : forall dl n r c,
      length dl = r -> width dl c ->
      dldotdl dl (dnil n) == dlzero Azero r n.
  Proof.
    intros dl n r. revert dl n. induction r; intros; simpl; auto.
    - apply List.length_zero_iff_nil in H. subst. reflexivity.
    - destruct dl; simpl in *. lia. inversion H. inversion H0.
      rewrite IHr with (c:=c); auto. rewrite H2.
      rewrite dlzero_Sr. f_equiv. rewrite ldotdl_nil_r. easy.
  Qed.

  (** dldotdl zero dl = zero *)
  Lemma dldotdl_zero_l : forall r dl c,
      width dl c ->
      dldotdl (dlzero Azero r c) dl == dlzero Azero r (length dl).
  Proof.
    induction r; simpl; intros; simpl; unfold dlzero in *; simpl; try easy.
    rewrite (IHr _ c); auto.
    erewrite (ldotdl_zero_l _); auto. easy.
  Qed.
  
  (** dldotdl dl zero = zero *)
  Lemma dldotdl_zero_r : forall dl c t,
      width dl c ->
      dldotdl dl (dlzero Azero t c) == dlzero Azero (length dl) t.
  Proof.
    induction dl; simpl; intros; auto. inv H.
    unfold dlzero; simpl. f_equiv; auto.
    - rewrite dlzero_rw. rewrite ldotdl_zero_r; auto. easy.
    - apply IHdl. auto.
  Qed.
  
  (** dltrans for dldotdl with right decomposition *)
  Lemma dltrans_dldotdl_right : forall d1 d2 l2 r,
      dltrans (dldotdl d1 (l2 :: d2)) (S r) ==
        (ldotdl l2 d1) :: (dltrans (dldotdl d1 d2) r).
  Proof.
    unfold width; induction d1; intros; simpl in *. easy.
    specialize (IHd1 d2 l2 r).
    destruct (dltrans (dldotdl d1 (l2 :: d2)) (S r)); try easy. inv IHd1.
    f_equiv. f_equiv; auto. apply ldot_comm. f_equiv. auto.
  Qed.
  
  (** dldotdl commutation *)
  Lemma dldotdl_comm : forall d1 d2 r c,
      length d1 = r -> width d1 c -> width d2 c ->
      dldotdl d1 d2 == dltrans (dldotdl d2 d1) r.
  Proof.
    induction d1; simpl; intros; subst.
    - rewrite dldotdl_nil_r. rewrite dltrans_nil. easy.
    - inv H0. rewrite dltrans_dldotdl_right.
      f_equiv; try easy. apply IHd1 with (c:=length a); auto.
  Qed.
  
  (** l * (d1 . d2)^T = (l . d1^T) . d2 *)
  Lemma ldotdl_dldotdl_dltrans_assoc : forall d1 d2 l {r c},
      width d1 c ->
      length d2 = r -> width d2 c ->
      (ldotdl l (dltrans (dldotdl d1 d2) r) ==
         ldotdl (ldotdl l (dltrans d1 c)) d2)%list.
  Proof.
    unfold width. induction d1; intros.
    - subst. simpl. rewrite ?ldotdl_nil_r.
      rewrite ldotdl_zero_l with (r:=length d2); auto. easy.
    - inv H. simpl. destruct l.
      + rewrite ldotdl_nil_l with (r:=length d2).
        2:{ apply consc_length.
            apply ldotdl_length; auto.
            apply dltrans_length. apply dldotdl_width with (c:=length a); auto. }
        rewrite ldotdl_nil_l with (r:=length a).
        2:{ apply consc_length; auto.
            apply dltrans_length; auto. }
        rewrite ldotdl_zero_l with (r:=length d2); auto. easy.
      + erewrite ldotdl_consr_consc with (r:=length d1);
          auto using dltrans_length, dltrans_width.
        2:{ rewrite dltrans_length.
            rewrite ldotdl_length with (r:=length d2); auto.
            apply dldotdl_width with (c:=length a); auto. }
        2:{ apply dltrans_width. apply dldotdl_length; auto.
            apply dldotdl_width with (c:=length a); auto. }
        rewrite ldotdl_consr_consc with (r:=length d1) (c:=length a);
          auto using dltrans_length, dltrans_width.
        erewrite ldotdl_lcmul_assoc with (r:=length a); auto.
        rewrite ldotdl_ladd_distr_r with (r:=length a) (c:=length d2);
          auto using lcmul_length, ldotdl_length, dltrans_length.
        rewrite IHd1 with (c:=length a); auto. easy.
  Qed.

  (** dldotdl association *)
  Lemma dldotdl_assoc : forall d1 d2 d3 r c,
      width d2 c ->
      length d3 = r -> width d3 c ->
      dldotdl (dldotdl d1 (dltrans d2 c)) d3 == dldotdl d1 (dltrans (dldotdl d2 d3) r).
  Proof.
    induction d1; simpl; intros; auto. f_equiv.
    - rewrite ldotdl_dldotdl_dltrans_assoc with (c:=c); auto. easy.
    - apply IHd1; auto.
  Qed.
  
  (** dldotdl left with dlunit *)
  Lemma dldotdl_dlunit_l : forall (dl : dlist A) {c},
      width dl c -> 
      dldotdl (dlunit Azero 1 c) dl == dltrans dl c.
  Proof.
    induction dl; simpl; intros; try easy.
    - rewrite dldotdl_nil_r. rewrite dlunit_length. easy.
    - inversion H.
      rewrite dldotdl_consr_r with (c:=c); auto using dlunit_width.
      rewrite IHdl; auto. rewrite ldotdl_dlunit; easy.
  Qed.
  
  (** dldotdl right with dlunit *)
  Lemma dldotdl_dlunit_r : forall (dl : dlist A) {c},
      width dl c -> 
      dldotdl dl (dlunit Azero 1 c) == dl.
  Proof.
    induction dl; simpl; intros; auto. inversion H.
    rewrite IHdl; auto. rewrite ldotdl_dlunit; easy.
  Qed.
  
End ldotdl_dldotdl.


(* ===================================================================== *)
(** ** Properties of dlcmul *)
Section dlcmul_properties.
  Context `{F:Field}.
  Context {AeqDec: Dec Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.

  Notation lcmul := (fun k l => map (fun x : A => Amul k x) l).
  Notation dlcmul := (fun k dl => map (map (fun x : A => Amul k x)) dl).
  
  (** Mapping cmul to dlist keep unchanged imply k = 1 or dlist is zero *)
  Lemma dlcmul_eq_imply_k1_or_dlzero : 
    forall {r c} k (dl : dlist A) (H1 : length dl = r) (H2 : width dl c),
      dlcmul k dl == dl -> ((k == 1)%A \/ dl == dlzero 0 r c).
  Proof.
    induction r; intros; simpl in *.
    - rewrite List.length_zero_iff_nil in H1. subst. right. auto.
    - destruct dl; simpl in *; try easy. inv H1. inv H2. inv H.
      specialize (IHr (length l) k dl eq_refl H4 H6).
      apply lcmul_eq_imply_k1_or_lzero with (n:=length l) in H3; auto.
      destruct IHr; auto. destruct H3; auto.
      right. simpl. rewrite dlzero_Sr. f_equiv; auto.
  Qed.

  (** Mapping cmul to dlist got zero imply k = 0 or dlist is zero *)
  Lemma dlcmul_eq0_imply_k0_or_dlzero : 
    forall {r c} k (dl : dlist A) (H1 : length dl = r) (H2 : width dl c),
      map (map (fun x => Amul k x)) dl == (dlzero 0 r c) ->
      ((k == 0)%A \/ dl == dlzero 0 r c).
  Proof.
    induction r; intros; simpl in *.
    - rewrite List.length_zero_iff_nil in H1. subst. right. auto.
    - destruct dl; simpl in *; try easy. inv H1. inv H2. inv H.
      specialize (IHr (length l) k dl eq_refl H4 H6).
      apply lcmul_eq0_imply_k0_or_lzero in H3; auto.
      destruct IHr; auto. destruct H3; auto.
      right. simpl. rewrite dlzero_Sr. f_equiv; auto.
  Qed.
  
End dlcmul_properties.


(* ===================================================================== *)
(** ** Set element or row of a dlist *)

Section dlset.
  Context `{Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.

  (** *** Set element of a dlist with a given element *)
  
  (** dl[i,j] <- x *)
  Fixpoint dlset (dl : dlist A) (i j : nat) (x : A) : dlist A :=
    match dl, i with
    | [], _ => []
    | l :: dl, 0 => (lset l j x) :: dl
    | l :: dl, S i' => l :: (dlset dl i' j x)
    end. 
  
  (** Length property *)
  Lemma dlset_length : forall dl i r j x,
      length dl = r -> length (dlset dl i j x) = r.
  Proof.
    intros dl; induction dl; auto. destruct i; intros; auto; simpl in *.
    destruct r; auto. easy.
  Qed.
  
  (** Width property *)
  Lemma dlset_width : forall dl i c j x, 
      width dl c -> width (dlset dl i j x) c.
  Proof.
    unfold width. intros dl; induction dl; auto.
    destruct i; intros; simpl in *; auto; inv H0; constructor; auto.
    apply lset_length; auto.
  Qed.

  (** *** Set element of a dlist with a function *)

  (** dl[i,j] <- f i j. This is inner loop: ix is changing every loop *)
  Fixpoint dlsetfAux (dl : dlist A) (i ix j : nat) (f : nat -> nat -> A) : dlist A :=
    match dl, ix with
    | [], _ => []
    | l :: dl, 0 => (lsetf l j (f i)) :: dl
    | l :: dl, S ix' => l :: (dlsetfAux dl i ix' j f)
    end. 

  (** dl[i,j] <- f i j *)
  Definition dlsetf (dl : dlist A) (i j : nat) (f : nat -> nat -> A) : dlist A :=
    dlsetfAux dl i i j f.

  Lemma dlsetfAux_length : forall dl i r i0 j f, 
      length dl = r -> length (dlsetfAux dl i0 i j f) = r.
  Proof. induction dl; auto. destruct i,r; auto; simpl; intros; auto. easy. Qed.
  
  Lemma dlsetf_length : forall dl r i j f, 
      length dl = r -> length (dlsetf dl i j f) = r.
  Proof. intros. apply dlsetfAux_length. auto. Qed.
  
  Lemma dlsetfAux_width : forall dl i c i0 j f, 
      width dl c -> width (dlsetfAux dl i0 i j f) c.
  Proof.
    unfold width. induction dl; auto. 
    induction i; intros; simpl in *; auto; inv H0; constructor; auto.
    apply lsetf_length; auto.
  Qed.
  
  Lemma dlsetf_width : forall dl i c j f, width dl c -> width (dlsetf dl i j f) c.
  Proof. intros. apply dlsetfAux_width; auto. Qed.

  (** *** Set row of a dlist with a list *)

  (** dl[i] <- x *)
  Fixpoint dlsetRow (dl : dlist A) (i : nat) (x : list A) : dlist A :=
    match dl, i with
    | [], _ => []
    | l :: dl, 0 => x :: dl
    | l :: dl, S i' => l :: (dlsetRow dl i' x)
    end. 
  
  Lemma dlsetRow_length : forall dl i r x, 
      length dl = r -> length (dlsetRow dl i x) = r.
  Proof.
    induction dl; auto. destruct i,r; auto; intros; simpl in *; auto. easy.
  Qed.
  
  (** Width property *)
  Lemma dlsetRow_width : forall dl i c x,
      length x = c -> width dl c -> width (dlsetRow dl i x) c.
  Proof.
    unfold width; induction dl; auto.
    induction i; intros; simpl in *; inv H1; constructor; auto.
  Qed.

  (** Set row keep unchanged if the row index is out-of-bound *)
  Lemma dlsetRow_rowIdxOutOfBound : forall dl i r c l,
      length dl = r -> width dl c -> i >= r -> dlsetRow dl i l == dl.
  Proof.
    intros dl i. revert dl. induction i; intros; simpl.
    - assert (r = 0) by lia. subst. apply List.length_zero_iff_nil in H3.
      subst. auto.
    - destruct dl; simpl in *; auto. destruct r; try lia. f_equiv.
      apply IHi with r c; auto; try lia. inv H1; auto.
  Qed.

  (** *** Set row of a dlist with a function *)

  (** dl[i] <- f i. This is inner loop: ix is changing every loop *)
  Fixpoint dlsetRowfAux (dl : dlist A) (i ix : nat) (f : nat -> list A) : dlist A :=
    match dl, ix with
    | [], _ => []
    | l :: dl, 0 => (f i) :: dl
    | l :: dl, S ix' => l :: (dlsetRowfAux dl i ix' f)
    end. 
  
  (** dl[i] <- f i *)
  Definition dlsetRowf (dl : dlist A) (i : nat) (f : nat -> list A) : dlist A :=
    dlsetRowfAux dl i i f.
  
  (** Length property *)
  Lemma dlsetRowfAux_length : forall dl ix r i f, 
      length dl = r -> length (dlsetRowfAux dl i ix f) = r.
  Proof.
    induction dl; auto. induction ix,r; intros; simpl in *; auto. easy.
  Qed.
  
  Lemma dlsetRowf_length : forall dl r i f, length dl = r -> length (dlsetRowf dl i f) = r.
  Proof. intros. apply dlsetRowfAux_length. auto. Qed.

  Lemma dlsetRowfAux_width : forall dl ix c i f, 
      length (f i) = c -> width dl c -> width (dlsetRowfAux dl i ix f) c.
  Proof.
    unfold width; intros dl; induction dl; auto. 
    induction ix; intros; simpl in *; auto; inv H1; constructor; auto.
  Qed.
  
  Lemma dlsetRowf_width : forall dl i c f, 
      length (f i) = c -> width dl c -> width (dlsetRowf dl i f) c.
  Proof.
    intros. apply dlsetRowfAux_width; auto.
  Qed.

End dlset.

Section test.
  (* Compute dlset [] 0 1 9. *)
  (* Compute dlset [[1;2];[3;4;5]] 0 1 9. *)
  (* Compute dlset [[1;2];[3;4;5]] 1 1 9. *)
  (* Compute dlset [[1;2];[3;4;5]] 2 1 9. *)
  (* Compute dlset [[1;2];[3;4;5]] 1 5 9. *)

  (* Let f_gen := fun (i j : nat) => (i + j + 10). *)
  (* Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 0 f_gen. *)
  (* Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 1 f_gen. *)
  (* Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 2 f_gen. *)
  (* Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 3 f_gen. *)
  (* Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 4 f_gen. *)
  (* Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 0 f_gen. *)
  (* Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 1 f_gen. *)
  (* Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 2 f_gen. *)
  (* Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 3 f_gen. *)
  (* Compute dlsetf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 4 f_gen. *)

  (* Compute dlsetRow [] 0 [8;9]. *)
  (* Compute dlsetRow [[1;2];[3;4;5]] 0 [8;9]. *)
  (* Compute dlsetRow [[1;2];[3;4;5]] 1 [8;9]. *)
  (* Compute dlsetRow [[1;2];[3;4;5]] 2 [8;9].   *)
  
  (* Let f_gen := fun (i : nat) => [i+10;i+11;i+12]. *)
  (* Compute dlsetRowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 f_gen. *)
  (* Compute dlsetRowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 f_gen. *)
  (* Compute dlsetRowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 2 f_gen. *)
  (* Compute dlsetRowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 3 f_gen.  *)

End test.


(* ===================================================================== *)
(** ** Row Transformation of a dlist *)
Section RowTransformation.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).

  Infix "==" := (Aeq) : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (eqlistA (eqlistA Aeq)) : dlist_scope.
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.

  Notation ladd := (map2 Aadd).
  Notation lcmul := (fun a l => map (fun x => a * x) l).
  
  (* Notation "- b" := (Aopp b) : A_scope. *)
  (* Notation Asub := (fun a b => a + (-b)). *)
  (* Infix "-" := Asub : A_scope. *)
  (* Notation "0" := Azero : A_scope. *)
  (* Notation "1" := Aone : A_scope. *)

  (** *** Swap two rows *)

  (** Swap row i1 and row i2 *)
  Definition dlistRowSwap (dl : dlist A) (i1 i2 : nat) : dlist A :=
    let r := length dl in
    if (i1 <? r) && (i2 <? r)
    then 
      let row_i1 := nth i1 dl [] in
      let row_i2 := nth i2 dl [] in
      dlsetRow (dlsetRow dl i1 row_i2) i2 row_i1
    else dl.
  
  (** Index out-of-bound *)
  Lemma dlistRowSwap_idxOutOfBound_i1 : forall dl r c i1 i2,
      length dl = r -> width dl c -> i1 >= r -> dlistRowSwap dl i1 i2 == dl.
  Proof.
    intros. unfold dlistRowSwap.
    rewrite H in *. apply Nat.ltb_ge in H1. rewrite H1; simpl. easy.
  Qed.

  (** Index out-of-bound *)
  Lemma dlistRowSwap_idxOutOfBound_i2 : forall dl r c i1 i2,
      length dl = r -> width dl c -> i2 >= r -> dlistRowSwap dl i1 i2 == dl.
  Proof.
    intros. unfold dlistRowSwap.
    rewrite H in *. apply Nat.ltb_ge in H1. rewrite H1; simpl.
    rewrite andb_false_r. easy.
  Qed.

  (** Length property *)
  Lemma dlistRowSwap_length : forall dl r c i1 i2, 
      length dl = r -> width dl c -> length (dlistRowSwap dl i1 i2) = r.
  Proof.
    intros. unfold dlistRowSwap.
    rewrite H in *. destruct (i1 <? r) eqn:E1, (i2 <? r) eqn:E2; simpl; auto.
    repeat rewrite dlsetRow_length with (r:=r); auto.
  Qed.

  (** Width property *)
  Lemma dlistRowSwap_width : forall dl r c i1 i2,
      length dl = r -> width dl c -> width (dlistRowSwap dl i1 i2) c.
  Proof.
    intros. unfold dlistRowSwap.
    rewrite H in *. destruct (i1 <? r) eqn:E1, (i2 <? r) eqn:E2; simpl; auto.
    repeat apply dlsetRow_width; auto; apply dlist_nth_length; auto; try lia;
      rewrite H in *; solve_nat_ineq.
  Qed.

  
  (** *** K times of one row *)

  (** k times of row i  *)
  Definition dlistRowK (dl : dlist A) (i : nat) (k : A) : dlist A :=
    let r := length dl in
    if (i <? r)
    then 
      let row_i := nth i dl [] in
      let row_i_K := lcmul k row_i in
      dlsetRow dl i row_i_K
    else dl.

  (** Index out-of-bound *)
  Lemma dlistRowK_idxOutOfBound : forall dl r c i k,
      length dl = r -> width dl c -> i >= r -> dlistRowK dl i k == dl.
  Proof.
    intros. unfold dlistRowK.
    rewrite H in *. apply Nat.ltb_ge in H1. rewrite H1; simpl. easy.
  Qed.

  (** Length property *)
  Lemma dlistRowK_length : forall dl r c i k,
      length dl = r -> width dl c -> length (dlistRowK dl i k) = r.
  Proof.
    intros. unfold dlistRowK.
    rewrite H in *. destruct (i <? r) eqn:Ei; simpl; auto.
    repeat rewrite dlsetRow_length with (r:=r); auto.
  Qed.

  (** Width property *)
  Lemma dlistRowK_width : forall dl r c i k,
      length dl = r -> width dl c -> width (dlistRowK dl i k) c.
  Proof.
    intros. unfold dlistRowK.
    rewrite H in *. destruct (i <? r) eqn:Ei; simpl; auto.
    repeat apply dlsetRow_width; auto.
    rewrite lcmul_length with (n:=c); auto.
    apply dlist_nth_length; auto; try lia; rewrite H in *; solve_nat_ineq.
  Qed.
  
  (** *** Add K times of one row to another row *)

  (** row(i2) = row(i2) + k * row(i1) *)
  Definition dlistRowKAdd (dl : dlist A) (i1 i2 : nat) (k : A) : dlist A :=
    let r := length dl in
    if (i1 <? r) && (i2 <? r)
    then 
      let row_i1 := nth i1 dl [] in
      let row_i2 := nth i2 dl [] in
      let row_i2' := ladd (lcmul k row_i1) row_i2 in
      dlsetRow dl i2 row_i2'
    else dl.

  (** Index out-of-bound *)
  Lemma dlistRowKAdd_idxOutOfBound_i1 : forall dl r c i1 i2 k,
      length dl = r -> width dl c -> i1 >= r -> dlistRowKAdd dl i1 i2 k == dl.
  Proof.
    intros. unfold dlistRowKAdd.
    rewrite H in *. apply Nat.ltb_ge in H1. rewrite H1; simpl. easy.
  Qed.

  (** Index out-of-bound *)
  Lemma dlistRowKAdd_idxOutOfBound_i2 : forall dl r c i1 i2 k,
      length dl = r -> width dl c -> i2 >= r -> dlistRowKAdd dl i1 i2 k == dl.
  Proof.
    intros. unfold dlistRowKAdd.
    rewrite H in *. apply Nat.ltb_ge in H1. rewrite H1; simpl.
    rewrite andb_false_r. easy.
  Qed.

  (** Length property *)
  Lemma dlistRowKAdd_length : forall dl r c i1 i2 k,
      length dl = r -> width dl c -> length (dlistRowKAdd dl i1 i2 k) = r.
  Proof.
    intros. unfold dlistRowKAdd.
    rewrite H in *. destruct (i1 <? r) eqn:E1, (i2 <? r) eqn:E2; simpl; auto.
    repeat rewrite dlsetRow_length with (r:=r); auto.
  Qed.

  (** Width property *)
  Lemma dlistRowKAdd_width : forall dl r c i1 i2 k,
      length dl = r -> width dl c -> width (dlistRowKAdd dl i1 i2 k) c.
  Proof.
    intros. unfold dlistRowKAdd.
    rewrite H in *. destruct (i1 <? r) eqn:E1, (i2 <? r) eqn:E2; simpl; auto.
    repeat apply dlsetRow_width; auto.
    rewrite ladd_length with (n:=c); auto.
    rewrite lcmul_length with (n:=c); auto.
    apply dlist_nth_length; auto; try lia; rewrite H in *; solve_nat_ineq.
    apply dlist_nth_length; auto; try lia; rewrite H in *; solve_nat_ineq.
  Qed.
  
End RowTransformation.

Section test.
  Let dlistRowK := dlistRowK (Amul:=Nat.mul).
  Let dlistRowKAdd := dlistRowKAdd (Aadd:=Nat.add) (Amul:=Nat.mul).
  Let dl := [[1;2];[3;4];[5;6]].
  (* Compute dlistRowSwap dl 0 1. *)
  (* Compute dlistRowK dl 0 2. *)
  (* Compute dlistRowKAdd dl 0 1 2. *)
End test.


(* ===================================================================== *)
(** ** Get or drop first n columns of a dlist *)
Section dlfirstnC_dlskipnC.
  Context {A : Type} {Azero : A}.

  (** *** Get first n columns of a dlist *)
  
  Fixpoint dlfirstnC (n : nat) (dl : dlist A) : dlist A :=
    match dl with
    | [] => []
    | l :: dl' => (firstn n l) :: (dlfirstnC n dl')
    end.

  Lemma dlfirstnC_length : forall dl r n, length dl = r -> length (dlfirstnC n dl) = r.
  Proof.
    induction dl; intros; simpl in *; auto.
    destruct r. lia. rewrite IHdl with (r:=r); auto.
  Qed.
  
  Lemma dlfirstnC_width : forall (dl : dlist A) c n,
      width dl c -> n < c -> width (dlfirstnC n dl) n.
  Proof.
    induction dl; intros; simpl in *; auto. constructor. inversion H.
    constructor; auto. rewrite firstn_length. lia. apply IHdl with (c:=c); auto.
  Qed.

  Lemma dlfirstnC_overflow : forall dl r c n,
      length dl = r -> width dl c -> n >= c -> dlfirstnC n dl = dl.
  Proof.
    induction dl; intros; auto. simpl. destruct r; simpl in *. lia.
    inversion H. inversion H0. f_equal; auto.
    - apply firstn_all2. lia.
    - apply IHdl with (r:=r)(c:=c); auto.
  Qed.

  (** *** Drop first n columns of a dlist *)

  Fixpoint dlskipnC (n : nat) (dl : dlist A) : dlist A :=
    match dl with
    | [] => []
    | l :: dl' => (skipn n l) :: (dlskipnC n dl')
    end.

  Lemma dlskipnC_length : forall dl r n, length dl = r -> length (dlskipnC n dl) = r.
  Proof.
    induction dl; intros; simpl in *; auto.
    destruct r. lia. rewrite IHdl with (r:=r); auto.
  Qed.
  
  Lemma dlskipnC_width : forall (dl : dlist A) c n,
      width dl c -> n < c -> width (dlskipnC n dl) (c - n).
  Proof.
    induction dl; intros; simpl in *; auto. constructor. inversion H.
    constructor; auto. rewrite skipn_length. lia. apply IHdl with (c:=c); auto.
  Qed.

  Lemma dlskipnC_overflow : forall dl r c n,
      length dl = r -> width dl c -> n >= c -> dlskipnC n dl = dnil r.
  Proof.
    induction dl; intros; simpl in *; auto.
    - subst. auto.
    - destruct r; simpl in *. lia. inversion H. inversion H0.
      rewrite IHdl with (r:=r)(c:=c); auto. f_equal; auto.
      rewrite skipn_all2; auto. lia.
  Qed.
End dlfirstnC_dlskipnC.
  

(* ===================================================================== *)
(** ** Remove one row or (and) one column of a dlist *)
Section dlremove.
  Context {A : Type} {Azero : A}.

  (** *** Remove one row of a dlist *)

  (* old definition *)
  (*
  Definition dlremoveRow (dl : dlist A) (i : nat) : dlist A :=
    (firstn i dl) ++ (skipn (S i) dl).

  Lemma dlremoveRow_length : forall dl r i,
      length dl = (S r) -> i < S r -> length (dlremoveRow dl i) = r.
  Proof.
    intros. unfold dlremoveRow.
    rewrite app_length.
    rewrite firstn_length, skipn_length. lia.
  Qed.
    
  Lemma dlremoveRow_width : forall dl c i,
      width dl c -> width (dlremoveRow dl i) c.
  Proof.
    intros. unfold dlremoveRow. apply app_width. split.
    apply firstn_width; auto. apply skipn_width; auto.
  Qed.
   *)

  Fixpoint dlremoveRow (dl : dlist A) (i : nat) : dlist A :=
    match dl with
    | [] => []
    | l :: dl' => match i with
                 | O => dl'
                 | S i' => l :: (dlremoveRow dl' i')
                 end
    end.

  Lemma dlremoveRow_length : forall dl r i,
      length dl = (S r) -> i < S r -> length (dlremoveRow dl i) = r.
  Proof.
    induction dl; intros; simpl in *. lia. destruct i; auto.
    destruct r; try lia. simpl. rewrite IHdl with (r:=r); auto. lia.
  Qed.
    
  Lemma dlremoveRow_width : forall dl c i,
      width dl c -> width (dlremoveRow dl i) c.
  Proof.
    induction dl; intros; simpl in *; auto.
    apply cons_width_iff in H. destruct H. destruct i; auto.
    apply cons_width_iff. split; auto.
  Qed.
  
  (** *** Remove one column of a dlist *)

  Definition dlremoveCol (dl : dlist A) (i : nat) : dlist A :=
    (dlfirstnC i dl) @@ (dlskipnC (S i) dl).

  Lemma dlremoveCol_length : forall dl r i,
      length dl = r -> length (dlremoveCol dl i) = r.
  Proof.
    intros. unfold dlremoveCol. rewrite dlappc_length with (r:=r); auto.
    rewrite dlfirstnC_length with (r:=r); auto.
    rewrite dlskipnC_length with (r:=r); auto.
  Qed.
  
  Lemma dlremoveCol_width : forall (dl : dlist A) c i,
      width dl (S c) -> i < (S c) -> width (dlremoveCol dl i) c.
  Proof.
    intros. unfold dlremoveCol.
    replace c with (i + (S c - (S i))); try lia. apply dlappc_width.
    apply dlfirstnC_width with (c:=S c); auto.
    destruct (i =? c) eqn:Ei.
    - apply Nat.eqb_eq in Ei. subst.
      rewrite dlskipnC_overflow with (r:=length dl) (c:=S c); auto.
      rewrite Nat.sub_diag. apply dnil_width.
    - apply Nat.eqb_neq in Ei.
      apply dlskipnC_width with (c:=S c); auto. lia.
  Qed.
  
  (** *** Remove one row and one column of a dlist *)

  Definition dlremove (dl : dlist A) (i j : nat) : dlist A :=
    dlremoveCol (dlremoveRow dl i) j.

  Lemma dlremove_length : forall dl r c i j,
      length dl = (S r) -> width dl c -> i < S r -> j < c ->
      length (dlremove dl i j) = r.
  Proof.
    intros. unfold dlremove.
    rewrite dlremoveCol_length with (r:=r); auto.
    rewrite dlremoveRow_length with (r:=r); auto.
  Qed.
  
  Lemma dlremove_width : forall dl r c i j,
      length dl = r -> width dl (S c) -> i < r -> j < S c ->
      width (dlremove dl i j) c.
  Proof.
    intros. unfold dlremove.
    apply dlremoveCol_width; auto. apply dlremoveRow_width; auto.
  Qed.

End dlremove.

Section test.
  Let dl := [[1;2;3];[4;5;6];[7;8;9]].
  (* Compute dlskipnC 3 []. *)
  (* Compute dlskipnC 3 dl. *)
  (* Compute dlremove dl 1 1. *)
End test.

(* ======================================================================= *)
(** ** Special search algorithm *)
Section search.
  Context `{Dec A Alt}.
  Infix "<?" := dec : A_scope.

  (** Find the minimum element from a list *)
  Section list_min.
    
    (** Find the minimum element from a list (Auxiliary function).
<<
      Parameters:
      l         the given list
      val       minimum value, init is the head of l
         
      Return:
      if the given list is empty, return val
      otherwise, return the value we need.
>>
     *)
    Fixpoint list_min_aux (l : list A) (val : A) : A :=
      match l with
      | [] => val
      | a :: tl =>
          if a <? val
          then list_min_aux tl a
          else list_min_aux tl val
      end.

    (** Find the minimum element from a list.
<<
      Parameters:
      l     the given list
      def   default value of A
         
      Return:
      if the given list is empty, return `def`
      otherwise, return the value we need.
>>
     *)
    Definition list_min (l : list A) (def : A) : A := list_min_aux l (hd def l).
  End list_min.

  (** Find the index of the minimum element from a list *)
  Section list_minPos.

    (** Find the index of the minimum element from a list (Auxiliary function).
<<
      Parameters:
      l         the given list
      minVal   minimum value, init is the head of l
      minPos   record position where the element is minum, init is 0
      cnt       to count the position, init is 0
         
      Return:
      if the given list is empty, return minPos
      otherwise, return the value we need.
>>
     *)
    Fixpoint list_minPos_aux (l : list A) (minVal : A) (minPos : nat) (cnt : nat) : nat :=
      match l with
      | [] => minPos
      | a :: tl =>
          if a <? minVal 
          then list_minPos_aux tl a cnt (S cnt)
          else list_minPos_aux tl minVal minPos (S cnt)
      end.

    (** Find the index of the minimum element from a list.
<<
      Parameters:
      l    the given list
         
      Return:
      if the given list is empty, return 0
      otherwise, return the value we need.
>>
     *)
    Definition list_minPos (l : list A) : nat :=
      match l with
      | [] => 0
      | hl :: tl => list_minPos_aux l hl 0 0
      end.

    (** Spec: no any other elements is smaller than the result. *)
    Lemma list_minPos_spec : forall (l : list A) (Azero : A),
        let minPos :=  list_minPos l in
        let minVal := nth minPos l Azero in
        Forall (fun a => if a <? minVal then false else true) l.
    Proof.
      intros *. induction l; constructor.
    Abort.
  End list_minPos.
End search.

Section test.
  Open Scope nat.

  (* Tips, we must specify which comparison relation will be used,
     othewise, the Coq system will "randomly" choose one depends on
     the sequence of the Instance declaration.
     
     For example, we need "<" here, but the system select "<=". *)
  Notation list_min := (list_min (Alt:=Nat.lt)).
  Notation list_minPos := (list_minPos (Alt:=Nat.lt)).
  
  (* Compute list_min [] 9. *)
  (* Compute list_min [2;3;4;1;5] 9. *)
  (* Compute list_min [2;3;4;1;1;5] 9. (* find the first minimum *) *)
  (* Compute list_min [1;2;3;4;5] 9. *)
  (* Compute list_min [2;3;4;5;1] 9. *)

  (* Compute list_minPos []. *)
  (* Compute list_minPos [2;3;4;1;5]. *)
  (* Compute list_minPos [2;3;4;1;1;5]. (* find the first minimum *) *)
  (* Compute list_minPos [1;2;3;4;5]. *)
  (* Compute list_minPos [2;3;4;5;1]. *)

End test.
