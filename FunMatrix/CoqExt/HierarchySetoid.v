(*
  Copyright 2024 ZhengPu Shi
  This file is part of FunMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Algebraic Hierarchy (Leibniz Equality version)
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. The motivate of this module is to support development with good organized 
    algebraic hierarchy, instead of scattered def./op./props.
  2. There are three technologies to form a hierarchy: module is a strong 
    specification and too heavy; type classes is used in Coq standard library;
    canonical structure is used in mathematical component.
  3. For type classes, ref to this paper "A Gentle Introduction to Type Classes 
    and Relations in Coq" and the refrence manual of Coq at 
    "https://coq.inria.fr/distrib/V8.13.2/refman/addendum/type-classes.html".
  4. About Q (rational number), we mainly use Qcanon (Qc) instead of Q, hence 
    the convenient of equality relation. Precisely, Qc use eq that has best 
    built-in support in Coq, rather than Q use Qeq that we should use Setoid 
    and write more code to let it work.
  5. Other references:
     (1) Arkansas Tech University / Dr. Marcel B. Finan /
         MATH 4033: Elementary Modern Algebra
     (2) 5 Definition and Examples of Groups
         https://faculty.atu.edu/mfinan/4033/absalg5.pdf
     (3) 14 Elementary Properties of Groups
         https://faculty.atu.edu/mfinan/4033/absalg14.pdf
     (4) https://math.okstate.edu/people/binegar/3613/3613-l21.pdf

  contents  :
  1. hierarchy structure
     Equivalence                    equivalent relation
     Dec Acmp                       decidable relation
     Injective phi Aeq              an operation is injective
     Surjective phi Aeq             an operation is surjective
     Bijective phi Aeq              an operation is bijective
     Homomorphic fa fb phi Aeq      if `phi (fa a1 a2) == fb (phi a1) (phi a2)`
     Homomorphism fa fb Aeq         ∃ phi, Homomorphic fa fb phi /\ Surjective phi
     Homomorphism2 fa fb g gb Aeq   ∃ phi, Homomorphic fa fb phi /\ 
                                    Homomorphic g gb phi /\ Surjective phi
     Associative f Aeq              an operation is associative
     Commutative f Aeq              an operation is commutative
     IdentityLeft f e Aeq           ∀ a, f e a == a
     IdentityRight f e Aeq          ∀ a, f a e == a
     DistrLeft Aadd Amul Aeq        ∀ a b c, a * (b + c) == a * b + a * c
     DistrRight Aadd Amul Aeq       ∀ a b c, (a + b) * c == a * c + b * c
     Order Aeq Alt Ale              order {==,<,<=}
     SGroup Aadd Aeq                semigroup {+,==}. Aadd is associative
     ASGroup Aadd Aeq               abelian semigroup {+,==}. Aadd is commutative
     Monoid Aadd Azero Aeq          monoid {+,0,==}
     AMonoid Aadd Azero Aeq         abelian monoid {+,0,==}
     Group Aadd Azero Aopp Aeq      group {+,0,-a,==}
     AGroup Aadd Azero Aopp Aeq     abelian group {+,0,-a,==}
     SemiRing Aadd Azero Amul Aone Aeq    semiring {+,0,*,1,==}
     Ring Aadd Azero Aopp Amul Aone Aeq   ring {+,0,-a,*,1}
     ARing Aadd Azero Aopp Amul Aone Aeq  abelian ring {+,0,-a,*,1}
     OrderedARing Aadd Azero Aopp Amul Aone Aeq Alt Ale   abelian-ring {+,0,-a,*,1} + order
     Field Aadd Azero Aopp Amul Aone Ainv  field {+,0,-a,*,1,/a}
     OrderedField Aadd Azero Aopp Amul Aone Ainv Aeq Alt Ale  field {+,0,-a,*,1,/a} + order
     ConvertToR Aadd Azero Aopp Amul Aone Ainv Aeq Alt Ale (a2r:A->R)
                The `a2r` operation is consistent
  
     ============= The structure of algebraic structure ===============

                  ARing     Field
                 /     \    /
              AGroup    Ring
             /     \    /
         AMonoid   Group
         /    \    /
     ASGroup  Monoid
        \     /
        SGroup

  2. tactics
     * SGroup
       sgroup             eliminate all same terms at head or tail
     * ASGroup
       move2h c           move an term to the head
       move2t c           move an term to the end
       asgroup            eliminate all same terms
     * Monoid, AMonoid
       monoid             eliminate identity element, and do "sgroup"
       amonoid            eliminate identity element, and do "asgroup"
     * Group, AGroup
       group              simplify equation with group propertity, and do "monoid"
       agroup             simplify equation with group propertity, and do "amonoid"
     * Ring, Field
       (built-in tactics) ring, ring_simplify, field, field_simply, field_simply_eq

  3. important lemmas
     * Ring
       make_ring_theory (H:ARing)      make a ring_theory, to use `ring` tactic.
     * Field
       make_field_theory (H:Field)     make a field_theory, to use `field` tactic.
 *)

Require Export Coq.Classes.CRelationClasses. (* binary_relation *)
Require Export Setoid. (*  *)
Require Import Coq.Logic.Description. (* constructive_definite_description *)
Require Export Basic.   (* reserved notation *)
Require Export BoolExt.
Require Export SetoidList. Import ListNotations.
Require Export Lia Lra.
Require Export Ring Field.
Require Import Arith ZArith QArith Qcanon Reals.

Open Scope nat_scope.
Open Scope A_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A Aeq Aadd Azero Aopp Amul Aone Ainv Adiv Alt.


(* ######################################################################### *)
(** * Small utilities *)

(** repeat split and intro *)
Ltac split_intro :=
  repeat (try split; try intro).

(** Applicate a unary function for n-times, i.e. f ( .. (f a0) ...) *)
Fixpoint iterate {A} (f : A -> A) (n : nat) (a0 : A) : A :=
  match n with
  | O => a0
  | S n' => f (iterate f n' a0)
  end.

Section test.
  Context {A} {f : A -> A} (Azero : A).
  (* Compute iterate f 3 Azero. *)
End test.

(* type should be: nat ->  *)


(* ######################################################################### *)
(** * <TEMPLATE structures> *)

(** ** Class *)

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * A relation is equivalence relation *)

(** ** Class *)

(* Global Hint Constructors Equivalence : core. *)

(** ** Theories *)

Section theories.
  Context `{Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  
  (** ~(a == b) -> ~(b == a) *)
  Lemma symmetry_not : forall (a b : A), ~(a == b) -> ~(b == a).
  Proof. intros. intro. destruct H0. easy. Qed.
End theories.

(** ~(a == b) -> ~(b == a) *)
Ltac symmetry_not :=
  apply symmetry_not.

(** ** Instances *)

(** ** Examples *)

Section examples.
  Context `{Equivalence A Aeq}.
  Infix "==" := Aeq : A_scope.
  
  (** ~(a == b) -> ~(b == a) *)
  Goal forall (a b : A), ~(a == b) -> ~(b == a).
  Proof. intros. symmetry_not. auto. Qed.
End examples.


(* ######################################################################### *)
(** * A relation is decidable *)

(** ** Class *)

Class Dec {A:Type} (Acmp:A->A->Prop) := {
    dec : forall (a b : A), {Acmp a b} + {~(Acmp a b)};
  }.

(* We prefer don't simpl `dec` *)
Arguments dec {A} _ {_} : simpl never.

(* Global Hint Constructors Dec : core. *)

(* equality relation is decidable *)
Definition Aeqdec {A} {AeqDec:Dec (@eq A)} := @dec _ (@eq A) AeqDec.

(** ** Theories *)
Section Theories.

  Context `(HDec: Dec).

  (** Tips: these theories are useful for R type *)
  
  (** Calculate equality to boolean, with the help of equality decidability *)
  Definition Acmpb (a b : A) : bool := if dec Acmp a b then true else false.

  (** Acmpb is true iff Acmp hold. *)
  Lemma Acmpb_true : forall a b, Acmpb a b = true <-> Acmp a b.
  Proof.
    intros. unfold Acmpb. destruct dec; split; intros; auto. easy.
  Qed.
  
  (** Acmpb is false iff Acmp not hold *)
  Lemma Acmpb_false : forall a b, Acmpb a b = false <-> ~(Acmp a b).
  Proof. intros. rewrite <- Acmpb_true. split; solve_bool. Qed.

  Lemma Acmp_reflect : forall a b : A, reflect (Acmp a b) (Acmpb a b).
  Proof. intros. unfold Acmpb. destruct (dec Acmp a b); constructor; auto. Qed.

  (* forall l1 l2 : list A, {l1 == l2} + {l1 <> l2} *)
  #[export] Instance list_Dec `{Dec _ (@eq A)} : Dec (@eq (list A)).
  Proof. constructor. intros. apply list_eq_dec. apply Aeqdec. Defined.

  Context {B : Type}.

  (** Equality of two pairs, iff their corresponding components are all equal. *)
  Lemma prod_eq_iff : forall (z1 z2 : A * B),
      z1 = z2 <-> fst z1 = fst z2 /\ snd z1 = snd z2.
  Proof.
    intros (a1,b1) (a2,b2). split; intros H; inv H; auto. simpl in *; subst; auto.
  Qed.

  (** Inequality of two pairs, iff at least one of components are not equal. *)
  Lemma prod_neq_iff : forall (z1 z2 : A * B),
      z1 <> z2 <-> fst z1 <> fst z2 \/ snd z1 <> snd z2.
  Proof.
    intros. rewrite prod_eq_iff. tauto.
  Qed.  

End Theories.

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Equivalence relation *)

(** ** Class *)

(* Equivalence is already in standard library *)

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Respect: an operation respect a relation (also known as "well-defined") *)

(* deprecated, replaced with "Proper" in Coq *)
(* Note that, the naming could be any of them:
    1. "add_wd", means "add" is well defined.
    2. "add_aeq", means "add" is a proper morphism about "aeq".
    3. "Qplus_comp", means "Qplus" is compatible to "Qeq".
*)

(** ** Class *)

(* (** A unary operation is respect to the equality relation *) *)
(* Class RespectUnary {A B:Type} (op:A->B) (Aeq:A->A->Prop) (Beq:B->B->Prop) := { *)
(*     respectUnary : forall x y : A, *)
(*       Aeq x y -> Beq (op x) (op y) *)
(*   }. *)

(* (** A binary operation is respect to the equality relation *) *)
(* Class RespectBinary {A B C:Type} (op:A->B->C) *)
(*   (Aeq:A->A->Prop) (Beq:B->B->Prop) (Ceq:C->C->Prop):= { *)
(*     respectBinary : forall x y : A, *)
(*       Aeq x y -> forall x0 y0 : B, Beq x0 y0 -> Ceq (op x x0) (op y y0) *)
(*   }. *)

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Injective *)

(** ** Class *)

Class Injective {A B} (phi: A -> B) := {
    injective : forall a1 a2 : A, a1 <> a2 -> phi a1 <> phi a2
  }.

(** ** Theories *)
Section Theories.
  Context {A B : Type}.
  
  (** Second form of injective *)
  Definition injective_form2 (phi: A -> B) :=
    forall a1 a2, phi a1 = phi a2 -> a1 = a2.

  (** These two forms are equal *)
  Lemma injective_eq_injective_form2 (phi: A -> B) :
    Injective phi <-> injective_form2 phi.
  Proof.
    split; intros.
    - hnf. destruct H as [H]. intros.
      specialize (H a1 a2). apply imply_to_or in H. destruct H.
      + apply NNPP in H. auto.
      + easy.
    - hnf in H. constructor. intros. intro. apply H in H1. easy.
  Qed.

  (** Injective function preserve equal relation *)
  Lemma injective_preserve_eq : forall (f : A -> B),
      Injective f -> (forall a1 a2, f a1 = f a2 -> a1 = a2).
  Proof.
    intros. apply injective_eq_injective_form2 in H. apply H. auto.
  Qed.

End Theories.
  
(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Surjective *)

(** ** Class *)

Class Surjective {A B} (phi: A -> B) := {
    surjective : forall b, (exists a, phi a = b)
  }.

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Bijective *)

(** ** Class *)

Class Bijective {A B} (phi: A -> B) := {
    bijInjective :: Injective phi;
    bijSurjective :: Surjective phi
  }.

(* Tips: About ":>", "::", coercion:
   1. use "::" or ":>" could be valid way to get inherited effect.
   2. "::" is advised way than ":>", from Coq 8.16, ":>" will give warning
   3. both "::" or ":>" have no coercion effect, even "::>" is no use.
      we can declare them manually use "Coercion xx : a >-> b".
      But note that, too many Coercion will give warning of "ambigous-paths" *)
Coercion bijInjective : Bijective >-> Injective.
Coercion bijSurjective : Bijective >-> Surjective.

(** ** Theories *)
Section Theories.
  Context {A B : Type}.
  
  (** There exist inverse function from a bijective function.

      ref: https://stackoverflow.com/questions/62464821/
      how-to-make-an-inverse-function-in-coq

      Tips: there are two methods to formalize "existential", sig and ex.
      ex makes a Prop, sig makes a Type. 
      Here, we proof the ex version. the sig version could be derived by an axiom:
      [constructive_definite_description : 
      forall (A : Type) (P : A -> Prop), (exists ! x : A, P x) -> {x : A | P x} ]
   *)

  Lemma bij_inverse_exist : forall (phi : A -> B) (Hbij: Bijective phi),
    {psi : B -> A | (forall a : A, psi (phi a) = a) /\  (forall b : B, phi (psi b) = b)}.
  Proof.
    intros. destruct Hbij as [Hinj [Hsurj]].
    apply injective_eq_injective_form2 in Hinj. hnf in *.
    assert (H : forall b, exists! a, phi a = b).
    { intros b.
      destruct (Hsurj b) as [a Ha]. exists a. repeat split; auto.
      intros a' Ha'. apply Hinj. rewrite Ha. auto. }
    apply constructive_definite_description.
    exists (fun b => proj1_sig (constructive_definite_description _ (H b))). split. 
    - split.
      + intros a. destruct (constructive_definite_description). simpl. auto.
      + intros b. destruct (constructive_definite_description). simpl. auto.
    - intro psi; intros. apply functional_extensionality.
      intros b. destruct (constructive_definite_description). simpl.
      destruct H0. rewrite <- e. auto.
  Defined.

  (** A bijective function preserve equal relation *)
  Lemma bijective_preserve_eq : forall (f : A -> B),
      Bijective f -> (forall (a1 a2 : A), f a1 = f a2 -> a1 = a2).
  Proof.
    intros. destruct H as [Hinj Hsurj].
    apply injective_preserve_eq in H0; auto.
  Qed.

End Theories.

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Homomorphic  *)

(** ** Class *)

Class Homomorphic {A B}
  (fa : A -> A -> A) (fb : B -> B -> B) (phi: A -> B) := {
    homomorphic : forall (a1 a2 : A), phi (fa a1 a2) = fb (phi a1) (phi a2)
  }.

(** ** Theories *)
Section Theories.
(* Definition homo_inj (phi : A -> B) : Prop := *)
(*   homomorphic phi /\ injective phi. *)

(* (** phi is a homomorphic and surjective mapping *) *)
(* Definition homo_surj (phi : A -> B) : Prop := *)
(*   homomorphic phi /\ surjective phi. *)
End Theories.

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Homomorphism *)

(** ** Class *)

(** If there exist a homomorphic and surjective mapping from <A,+> to <B,⊕>,
    then we said <A,+> and <B,⊕> is homomorphism *)
Class Homomorphism {A B} (fa : A -> A -> A) (fb : B -> B -> B) := {
    homomorphism : exists (phi: A -> B), Homomorphic fa fb phi /\ Surjective phi
  }.

(** If there exist two homomorphic and surjective mapping from <A,+> to <B,⊕>
    and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is homomorphism *)
Class Homomorphism2 {A B} (fa ga : A -> A -> A) (fb gb : B -> B -> B) := {
    homomorphism2 : exists (phi: A -> B),
      Homomorphic fa fb phi /\ Homomorphic ga gb phi /\ Surjective phi
  }.

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Isomorphism *)

(** ** Class *)

(** If there exist a homomorphic and bijective mapping from <A,+> to <B,⊕>,
    then we said <A,+> and <B,⊕> is isomorphism *)
Class Isomorphism {A B} (fa : A -> A -> A) (fb : B -> B -> B) := {
    isomorphism : exists (phi: A -> B), Homomorphic fa fb phi /\ Bijective phi
  }.

(** If there exist two homomorphic and bijective mapping from <A,+> to <B,⊕>
    and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is isomorphism *)
Class Isomorphism2 {A B} (fa ga : A -> A -> A) (fb gb : B -> B -> B) := {
    isomorphism2 : exists (phi: A -> B),
      Homomorphic fa fb phi /\ Homomorphic ga gb phi /\ Bijective phi
  }.

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Subset *)

(** ** Class *)
(* C is subset of P *)
Class Subset (C P : Type) := {
    sub_phi : C -> P;
    sub_phi_inj : Injective sub_phi
  }.

(** ** Theories *)

(** ** Instances *)

Instance nat_Z_Subset : Subset nat Z.
Proof.
  refine (@Build_Subset _ _ Z.of_nat _).
  rewrite injective_eq_injective_form2. hnf. apply Nat2Z.inj.
Qed.

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Associative *)

(** ** Class *)
Class Associative {A} (Aop : A -> A -> A) (Aeq : relation A) := {
    associative : forall a b c, Aeq (Aop (Aop a b) c) (Aop a (Aop b c));
  }.

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Commutative *)

(** ** Class *)
Class Commutative {A} (Aop : A -> A -> A) (Aeq : relation A) := {
    commutative : forall a b, Aeq (Aop a b) (Aop b a)
  }.

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Identity Left/Right *)

(** ** Class *)
Class IdentityLeft {A} (Aop : A -> A -> A) (Ae : A) (Aeq : relation A) := {
    identityLeft : forall a, Aeq (Aop Ae a) a
  }.

Class IdentityRight {A} (Aop : A -> A -> A) (Ae : A) (Aeq : relation A)  := {
    identityRight : forall a, Aeq (Aop a Ae) a
  }.

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Inverse Left/Right *)

(** ** Class *)
Class InverseLeft {A} (Aop : A -> A -> A) (Ae : A) (Ainv : A -> A)
  (Aeq : relation A) := {
    inverseLeft : forall a, Aeq (Aop (Ainv a) a) Ae
  }.

Class InverseRight {A} (Aop : A -> A -> A) (Ae : A) (Ainv : A -> A)
  (Aeq : relation A) := {
    inverseRight : forall a, Aeq (Aop a (Ainv a)) Ae
  }.

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Distributive *)

(** ** Class *)

(* Class DistrUnary {A} (Tadd:A -> A -> A) (Aopp : A -> A) := { *)
(*     distrUnary : forall a b, *)
(*       Aopp (Tadd a b) = Tadd (Aopp a) (Aopp b) *)
(*   }. *)

Class DistrLeft {A} (Aadd Amul : A -> A -> A) (Aeq : relation A) := {
    distrLeft : forall a b c,
      Aeq (Amul a (Aadd b c)) (Aadd (Amul a b) (Amul a c))
  }.

Class DistrRight {A} (Aadd Amul : A -> A -> A) (Aeq : relation A) := {
    distrRight : forall a b c,
      Aeq (Amul (Aadd a b) c) (Aadd (Amul a c) (Amul b c))
  }.

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Involution Law *)

(** ** Class *)

(* Class Involution {A : Type} (Aopp : A -> A) := { *)
(*     involution : forall a, Aopp (Aopp a) = a *)
(*   }. *)

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Semigroup *)

(** ** Class *)
Class SGroup {A} Aadd Aeq := {
    sgroupEquiv :: Equivalence Aeq;
    sgroupAssoc :: @Associative A Aadd Aeq;
    sgroupAaddProper :: Proper (Aeq ==> Aeq ==> Aeq) Aadd;
  }.
(* Coercion sgroupEquiv : SGroup >-> Equivalence. *)
(* Coercion sgroupAssoc : SGroup >-> Associative. *)
(* Coercion sgroupAaddProper : SGroup >-> Proper. *)


(** ** Theories *)

(* Eliminate head term in an expression over semi-group <op, aeq> *)
Ltac sgroup_head op aeq :=
  rewrite ?associative;
  repeat
    (try
       match goal with
       (* Tips: if there are Proper relation in the context, then 
        f_equiv = f_equal + reflexivity *)
       (* | |- aeq (op ?a _) (op ?a _) => 
          apply sgroupAaddProper; [reflexivity|] *)
       | |- aeq (op ?a _) (op ?a _) => f_equiv
       end;
     try easy).

(* Eliminate tail term in an expression over semi-group <op, aeq> *)
Ltac sgroup_tail op aeq :=
  rewrite <- ?associative;
  repeat
    (try
       match goal with
       | |- aeq (op _ ?a) (op _ ?a) => f_equiv
       end;
     try easy).

(** Simplify equality on semigroup <SG, op, aeq> *)
Ltac sgroup_core op aeq :=
  intros;
  try (progress (sgroup_head op aeq));
  try (progress (sgroup_tail op aeq)).

(** Simplify equality on semigroup in current context *)
Ltac sgroup :=
  match goal with
  | SG : SGroup ?op ?aeq |- _ => sgroup_core op aeq
  end.

(** ** Instances *)

(** ** Examples *)

Section test.
  Context `{HSGroup : SGroup}. Infix "+" := Aadd. Infix "==" := Aeq.

  (* Test bench *)
  Variable a b c d e f g h i j k : A.
                                                                    
  (* 1 level *)
  Goal b == k -> a + b == a + k. sgroup. Qed.
  Goal a == k -> a + b == k + b. sgroup. Qed.

  (* 2 levels *)
  Goal b + c == k -> a + b + c == a + k. sgroup. Qed.
  Goal c == k -> a + b + c == a + b + k. sgroup. Qed.
  Goal a + b == k -> a + b + c == k + c. sgroup. Qed.
  Goal a == k -> (a + b) + c == k + (b + c). sgroup. Qed.

  (* 3 levels *)
  Goal b + c + d == k -> a + b + c + d == a + k. sgroup. Qed.
  Goal c + d == k -> a + b + c + d == a + b + k. sgroup. Qed.
  Goal d == k -> a + b + c + d == a + b + c + k. sgroup. Qed.
  Goal a + b + c == k -> a + b + c + d == k + d. sgroup. Qed.
  Goal a + b == k -> a + b + c + d == k + c + d. sgroup. Qed.
  Goal a == k -> a + b + c + d == k + b + c + d. sgroup. Qed.
  
  (* 4 levels *)
  Goal b + c + d + e == k -> a + b + c + d + e == a + k. sgroup. Qed.
  Goal c + d + e == k -> a + b + c + d + e == a + b + k. sgroup. Qed.
  Goal d + e == k -> a + b + c + d + e == a + b + c + k. sgroup. Qed.
  Goal e == k -> a + b + c + d + e == a + b + c + d + k. sgroup. Qed.
  Goal a + b + c + d == k -> a + b + c + d + e == k + e. sgroup. Qed.
  Goal a + b + c == k -> a + b + c + d + e == k + d + e. sgroup. Qed.
  Goal a + b == k -> a + b + c + d + e == k + c + d + e. sgroup. Qed.
  Goal a == k -> a + b + c + d + e == k + b + c + d + e. sgroup. Qed.
End test.


(* ######################################################################### *)
(** * Abelian semigroup *)

(** ** Class *)
Class ASGroup {A} Aadd Aeq := {
    asgroupSGroup :: @SGroup A Aadd Aeq;
    asgroupComm :: Commutative Aadd Aeq
  }.
Coercion asgroupSGroup : ASGroup >-> SGroup.
(* Coercion asgroupComm : ASGroup >-> Commutative. *)

(** ** Theories *)

(** In a commutative semigroup, adjust a term in the equation to the head,
    and use full right associative form for next step of elimination.
    From: a1 + ... + c + ... + an    (with parentheses of any form)
    To  : c + (a1 + (... + an)) 
    在交换半群中，将等式里的一个项调整到头部，并使用完全的右结合形式以便下一步消去。*)
Ltac move2h c :=
  rewrite <- ?associative;
  try rewrite (commutative _ c);
  rewrite ?associative.

(** In a commutative semigroup, adjust a term in the equation to the tail,
    and use full left associative form for next step of elimination.
    From: a1 + ... + c + ... + an    (with parentheses of any form)
    To  : (...(a1 + ... + an)...) + c
    在交换半群中，将等式里的一个项调整到尾部，并使用完全的左结合形式以便下一步消去。*)
Ltac move2t c :=
  rewrite ?associative;
  try rewrite (commutative c);
  rewrite <- ?associative.

Section test.
  Context `{HASGroup : ASGroup}. Infix "+" := Aadd. Infix "==" := Aeq.
  Variable a0 a1 a2 a3 a4 a5 a6 : A.

  (* Example: any sub-term could be move to head, and finally reach equal *)
  Goal a0 + (a1 + a2) + a3 == a3 + (a0 + a2) + a1.
  Proof. do 2 move2h a0. do 2 move2h a1. do 2 move2h a2. do 2 move2h a3. easy. Qed.
  
  (* Example: any sub-term could be move to tail, and finally reach equal *)
  Goal a0 + (a1 + a2) + a3 == a3 + (a0 + a2) + a1.
  Proof. do 2 move2t a0. do 2 move2t a1. do 2 move2t a2. do 2 move2t a3. easy. Qed.
End test.

(** In a commutative semigroup, eliminate first common head.
    From: c + a1 + ... + an == c + b1 + ... + bm   (with parentheses of any form)
    To  : a1 + (a2 + (... + an)) == b1 + (b2 + (... + bm))
    在交换半群中，消去第一个相同的头部。 *)
Ltac elimh1 :=
  rewrite ?associative; (* assure fully right-associative form *)
  match goal with
  | |- ?aeq (?f ?c ?a) (?f ?c ?b) => f_equiv (* elim head on setoid *)
  end.

(** In a commutative semigroup, eliminate first common tail.
    From: a1 + ... + an + c == b1 + ... + bm + c   (with parentheses of any form)
    To  : ((a1 + a2) + ...) + an == ((b1 + b2) + ...) + bm 
    在交换半群中，消去第一个相同的尾部。 *)
Ltac elimt1 :=
  rewrite <- ?associative; (* assure fullly left-associative form *)
  match goal with
  | |- ?aeq (?f ?a ?c) (?f ?b ?c) => f_equiv
  end.

(* Automatically simplify expressions with Abelian semigroup structure (Try 1) *)
Section try1.
  (** In a commutative semigroup, eliminate all possible common head
    在交换半群中，自动消去左式中所有可能相同的头部 *)
  Ltac elimh :=
    rewrite ?associative; (* assure fully right-associative form *)
    repeat match goal with
      | |- ?aeq (?f ?c _) (?f _ _) => move2h c; elimh1
      end.
  
  (** In a commutative semigroup, eliminate all possible common tail 
    在交换半群中，自动消去左式中所有可能相同的尾部 *)
  Ltac elimt :=
    rewrite <- ?associative; (* assure fully left-associative form *)
    repeat match goal with
      | |- ?aeq (?f _ ?c) (?f _ _) => move2t c; elimt1
      end.

  (** In a commutative semigroup, eliminate all possible common head and tail
      在交换半群中，自动消去左式和右式中所有可能相同的头部和尾部 *)
  Ltac asgroup :=
    elimh; elimt; (* eliminate head and tail by left-side expression *)
    symmetry;
    elimh; elimt. (* eliminate head and tail by right-side expression *)

  Section test.
    Context `{HASGroup : ASGroup}. Infix "+" := Aadd. Infix "==" := Aeq.
    Variable a0 a1 a2 a3 a4 a5 a6 b1 b2 c1 c2 : A.

    (** CASE 1: if two sides are equal
        情形1：等式两侧完全相同 *)

    (* By manually move and eliminate every sub-term to the head
       调整到尾部+消去尾部，可实现化简 *)
    Goal a0 + (a1 + a2) + a3 == a3 + (a0 + a2) + a1.
    Proof.
      do 2 move2h a0; elimh1.
      do 2 move2h a1; elimh1.
      do 2 move2h a2; elimh1.
    Qed.

    (* By manually move and eliminate every sub-term to the tail
       调整到尾部+消去尾部，可实现化简 *)
    Goal a0 + (a1 + a2) + a3 == a3 + (a0 + a2) + a1.
    Proof.
      do 2 move2t a0; elimt1.
      do 2 move2t a1; elimt1.
      do 2 move2t a2; elimt1.
    Qed.

    (* Automatically eliminate every head by left-side expression
       使用左式消去头部 *)
    Goal a0 + (a1 + a2) + a3 == a3 + (a0 + a2) + a1.  Proof. elimh. Qed.
    (* Automatically eliminate every tail by left-side expression
       使用左式消去尾部 *)
    Goal a0 + (a1 + a2) + a3 == a3 + (a0 + a2) + a1.  Proof. elimt. Qed.
    (* Automatically eliminate every head by right-side expression
       使用右式消去头部 *)
    Goal a0 + (a1 + a2) + a3 == a3 + (a0 + a2) + a1.  Proof. symmetry. elimh. Qed.
    (* Automatically eliminate every tail by right-side expression
       使用右式消去尾部 *)
    Goal a0 + (a1 + a2) + a3 == a3 + (a0 + a2) + a1.  Proof. symmetry. elimt. Qed.

    (** CASE 2: if two sides are not equal
        情形2，等式两侧不完全相同 *)
    Let eq2 : Prop := a0 + (a1 + a2 + a3) + a4 + a5 == a2 + a0 + a6 + a3 + a4.

    (* Eliminate every head by left-side expression, but it is not complete
       使用左式消去头部，不完整 *)
    Goal eq2. unfold eq2. elimh. Abort.
    (* Eliminate every tail by left-side expression, but it is not complete
       使用左式消去尾部，不完整 *)
    Goal eq2. unfold eq2. elimt. Abort.
    (* Eliminate every head by right-side expression, but it is not complete
       使用右式消去头部，不完整 *)
    Goal eq2. unfold eq2. symmetry. elimh. Abort.
    (* Eliminate every tail by right-side expression, but it is not complete
       使用右式消去尾部，不完整 *)
    Goal eq2. unfold eq2. symmetry. elimt. Abort.
    (* Eliminate every tail by both side expression, it is complete
       使用左式及右式消去头部和尾部，完整 *)
    Goal eq2. unfold eq2. asgroup. Abort.

    (** CASE 3: if there is a common sub-term in the middle, neither the head nor the tail:
        情况3，某个相同的项出现中中间，既不在头部，也不在尾部 *)
    
    (* Eliminate every tail by both side expression, but it is not complete
       此时，并没有得到化简，只会不断的交换等式 *)
    Goal b1 + a0 + b2 == c1 + a0 + c2.
    Proof. asgroup. Abort.
    
    (* 也许能够设计一种方法来遍历左侧或右侧的所有的项，但暂时可以手工来做。
       比如，可以手工调用 move2h 或 move2t 来移动一个项，然后调用 elimh 或
       elimt 或 asgroup 来消除它 *)
    Goal b1 + a0 + b2 == c1 + a0 + c2.
    Proof.
      intros.
      do 2 move2h a0. asgroup.
      (* 达到了最简状态 *)
    Abort.
    
  End test.

  (* 总结：
     1. 当“等式左右两侧既无相同的头部，又无相同的尾部”时（简称，首尾无相同项），
        比如 b1 + a + b2 == c1 + a + c2 无法消去 a。
     2. 当首尾有相同项时，都能被消掉。
     3. 当等式不成立时，没有真正的终止状态，无法使用 repeat。
     4. 效率较低（数据有待测试）
   *)
End try1.

(* Automatically simplify expressions with Abelian semigroup structure (Try 2) *)
Section try2.
  (* 由于上一节中的策略无法化简 b1 + a + b2 == c1 + a + c2 的情形，
   即，两侧等式的头尾都没有相同元素时，就不会化简。
   同时，我们又不想手动使用 move2h 或 move2t 等策略来化简，
   所以设计了新的策略来帮助自动化简。
   思路：使用模式匹配确保等式两侧有相同的项，然后精确的消掉这个项。*)

  (** 在交换半群中，自动消去等式中相同的项 *)
  Ltac asgroup :=
    (* 处理为左结合的形式，消去尾部。（也可以处理为右结合然后消去头部） *)
    rewrite <- ?associative;
    (* 找出所有可能的匹配 *)
    repeat
      (match goal with
       (* 1 level *)
       | |- ?aeq (?f ?a _) (?f ?a _) => f_equiv
       | |- ?aeq (?f _ ?a) (?f _ ?a) => f_equiv
       | |- ?aeq (?f ?a _) (?f _ ?a) => do 2 move2t a
       | |- ?aeq (?f _ ?a) (?f ?a _) => do 2 move2t a
       (* 2 levels *)
       | |- ?aeq (?f (?f ?a _) _) (?f ?a _) => do 2 move2t a
       | |- ?aeq (?f (?f ?a _) _) (?f _ ?a) => do 2 move2t a
       | |- ?aeq (?f (?f _ ?a) _) (?f ?a _) => do 2 move2t a
       | |- ?aeq (?f (?f _ ?a) _) (?f _ ?a) => do 2 move2t a
       | |- ?aeq (?f ?a _) (?f (?f ?a _)) _ => do 2 move2t a
       | |- ?aeq (?f ?a _) (?f (?f _ ?a)) _ => do 2 move2t a
       | |- ?aeq (?f _ ?a) (?f (?f ?a _)) _ => do 2 move2t a
       | |- ?aeq (?f _ ?a) (?f (?f _ ?a)) _ => do 2 move2t a
       | |- ?aeq (?f (?f ?a _) _) (?f (?f ?a _) _) => do 2 move2t a
       | |- ?aeq (?f (?f ?a _) _) (?f (?f _ ?a) _) => do 2 move2t a
       | |- ?aeq (?f (?f _ ?a) _) (?f (?f ?a _) _) => do 2 move2t a
       | |- ?aeq (?f (?f _ ?a) _) (?f (?f _ ?a) _) => do 2 move2t a
       | |- ?aeq (?f (?f ?a _) _) (?f _ (?f ?a _)) => do 2 move2t a
       | |- ?aeq (?f (?f ?a _) _) (?f _ (?f _ ?a)) => do 2 move2t a
       | |- ?aeq (?f (?f _ ?a) _) (?f _ (?f ?a _)) => do 2 move2t a
       | |- ?aeq (?f (?f _ ?a) _) (?f _ (?f _ ?a)) => do 2 move2t a
       end;
       auto).

  Section test.
    Context `{HASGroup : ASGroup}. Infix "+" := Aadd. Infix "==" := Aeq.
    Variable a0 a1 a2 a3 a4 a5 a6 b1 b2 c1 c2 : A.

    (* 上一节中不能处理的例子已经可以自动化了 *)
    Goal b1 + a0 + b2 == c1 + a0 + c2.
    Proof. asgroup. Abort.

    (* 再复杂的模式又不能处理了，因为没有编写这样的模式 *)
    Goal b1 + a0 + a1 + b2 == c1 + a1 + a0 + c2.
    Proof. asgroup. Abort.
    
  End test.

  (* 但是，随着表达式的复杂度提升，需要写的模式会指数式增长，这是不可取的。
     同时，我们发现上述模式非常有规律，是否可以自动化？是的，利用 `context` *)
  
End try2.

(* Finally, we developed a more generalized tactic which can solve any cases,
   by using pattern match ability of `context` *)

(* handle structures smaller than this *)
Ltac asgroup_smaller :=
  match goal with
  | SG:SGroup ?op ?aeq |- _ => sgroup_core op aeq
  end.
  
(** Eliminate all possible common sub terms on Abelian semigroup <ASG, op, aeq>
    消去交换半群<ASG, op, aeq>上的所有可能相同的项 *)
Ltac asgroup_core op aeq :=
  intros;
  (* 此时使用左结合，然后每个相同的项移动至尾部来消去。（也可以右结合+头部) *)
  rewrite <- ?associative;
  repeat
    (match goal with
     | |- aeq ?A ?B =>
         (* 找出 A 中所有 a+b 的子表达式 *)
         match A with
         | context [op ?a ?b] =>
             (* 在 B 中找 a+c, c+a, c+b, b+c 这四种模式  *)
             match B with
             | context [op a _] => do 2 move2t a; f_equiv
             | context [op _ a] => do 2 move2t a; f_equiv
             | context [op b _] => do 2 move2t b; f_equiv
             | context [op _ b] => do 2 move2t b; f_equiv
             end
         end
     end;
     try easy);
  asgroup_smaller.

(** Eliminate all possible common sub terms on Abelian semigroup in current context
    消去上下文中交换半群上的所有可能相同的项 *)
Ltac asgroup :=
  try match goal with ASG:ASGroup ?op ?aeq |- _ => asgroup_core op aeq end;
  asgroup_smaller.

(** ** Instances *)

(** ** Examples *)

Section test.
  Context `{HASGroup : ASGroup}. Infix "+" := Aadd. Infix "==" := Aeq.

  (* Test bench *)
  Variable a b c d e f g h i j k : A.
  
  (* 1 level *)
  Goal b == k -> a + b == a + k. asgroup. Qed.
  Goal b == k -> b + a == k + a. asgroup. Qed.
  Goal b == k -> a + b == k + a. asgroup. Qed.
  Goal b == k -> b + a == a + k. asgroup. Qed.

  (* 2 levels *)
  Goal b + c == k -> a + b + c == a + k. asgroup. Qed.
  Goal b + c == k -> a + b + c == k + a. asgroup. Qed.
  Goal a + c == k -> a + b + c == b + k. asgroup. Qed.
  Goal a + c == k -> a + b + c == k + b. asgroup. Qed.

  (* 3 levels *)
  Goal b + c + d == k -> a + b + c + d == a + k. asgroup. Qed.
  Goal b + c + d == k -> a + b + c + d == k + a. asgroup. Qed.
  Goal a + c + d == k -> a + b + c + d == b + k. asgroup. Qed.
  Goal a + c + d == k -> a + b + c + d == k + b. asgroup. Qed.
  Goal a + b + c == k -> a + b + c + d == d + k. asgroup. Qed.
  Goal a + b + c == k -> a + b + c + d == k + d. asgroup. Qed.
  
  (* 4 levels *)
  Goal b + c + d + e == k -> a + b + c + d + e == a + k. asgroup. Qed.
  Goal b + c + d + e == k -> a + b + c + d + e == k + a. asgroup. Qed.
  Goal a + c + d + e == k -> a + b + c + d + e == b + k. asgroup. Qed.
  Goal a + c + d + e == k -> a + b + c + d + e == k + b. asgroup. Qed.
  Goal a + b + d + e == k -> a + b + c + d + e == c + k. asgroup. Qed.
  Goal a + b + d + e == k -> a + b + c + d + e == k + c. asgroup. Qed.
  Goal a + b + c + e == k -> a + b + c + d + e == d + k. asgroup. Qed.
  Goal a + b + c + e == k -> a + b + c + d + e == k + d. asgroup. Qed.
  Goal a + b + c + d == k -> a + b + c + d + e == e + k. asgroup. Qed.
  Goal a + b + c + d == k -> a + b + c + d + e == k + e. asgroup. Qed.
  
  (* 5 levels *)
  Goal a + b + c + d + f == k -> a + b + c + d + e + f == e + k. asgroup. Qed.
  Goal a + b + c + d + e == k -> a + b + c + d + e + f == f + k. asgroup. Qed.

  (* 5 levels，swapped left/right side *)
  Goal a + b + c + d + f == k -> e + k == a + b + c + d + e + f. asgroup. Qed.
  Goal a + b + c + d + e == k -> f + k == a + b + c + d + e + f. asgroup. Qed.

  (* if both expressions have different heads and tails *)
  Goal forall x1 x2 y1 y2 : A,
      x1 + x2 == y1 + y2 -> x1 + a + b + c + x2 == y1 + c + (b + a) + y2.
  Proof. asgroup. Qed.
End test.


(* ######################################################################### *)
(** * Monoid 幺半群、独异点 *)

(** ** Class *)
Class Monoid {A} Aadd Azero Aeq := {
    monoidSGroup :: @SGroup A Aadd Aeq;
    monoidIdL :: IdentityLeft Aadd Azero Aeq;
    monoidIdR :: IdentityRight Aadd Azero Aeq
  }.
Coercion monoidSGroup : Monoid >-> SGroup.
(* Coercion monoidIdL : Monoid >-> IdentityLeft. *)
(* Coercion monoidIdR : Monoid >-> IdentityRight. *)

Arguments monoidSGroup {A Aadd Azero Aeq}.
Arguments monoidIdL {A Aadd Azero Aeq}.
Arguments monoidIdR {A Aadd Azero Aeq}.


(** ** Theories *)

(* handle structures smaller than this *)
Ltac monoid_smaller :=
  match goal with
  | SG:SGroup ?op ?aeq |- _ => sgroup_core op aeq
  end.

(* Simplify expressions on monoid <M, op, e, aeq>, only new features of monoid *)
Ltac monoid_only op e aeq :=
  intros;
  repeat
    (try
       match goal with
       (* 0 + a = a *)
       | [M:Monoid op e aeq |- context [op e ?a]] =>
           rewrite (@identityLeft _ op e aeq (monoidIdL M) a) at 1
       | [M:Monoid op e aeq, H:context [op e ?a] |- _] =>
           rewrite (@identityLeft _ op e aeq (monoidIdL M) a) in H at 1
       (* a + 0 = a *)
       | [M:Monoid op e aeq |- context [op ?a e]] =>
           rewrite (@identityRight _ op e aeq (monoidIdR M) a) at 1
       | [M:Monoid op e aeq, H:context [op ?a e] |- _] =>
           rewrite (@identityRight _ op e aeq (monoidIdR M) a) in H at 1
       end;
     try easy).

(* Simplify expressions on monoid <M, op, e, aeq> *)
Ltac monoid_core op e aeq :=
  repeat
    (match goal with
     (* M + SG，则顺序执行二者 *)
     | M:Monoid op e aeq, SG:SGroup op aeq |- _ =>
         monoid_only op e aeq; sgroup_core op aeq
     (* M，则转换为 M + SG *)
     | M:Monoid op e aeq |- _ => pose proof (monoidSGroup M) as HSGroup
     end;
     try easy);
  monoid_smaller.

(* Simplify expressions on monoid in current context *)
Ltac monoid :=
  try match goal with M:Monoid ?op ?e ?aeq |- _ => monoid_core op e aeq end;
  monoid_smaller.


(** ** Instances *)
Section list.
  Import SetoidList.
  Context `{HMonoid : Monoid}.
  
  (** fold_left is a proper relation *)
  #[export] Instance fold_left_aeq :
    Proper (eqlistA Aeq ==> Aeq ==> Aeq) (fold_left Aadd).
  Proof.
    intros l1. induction l1; intros l2 Hl a1 a2 Ha.
    - inv Hl. simpl. auto.
    - destruct l2. easy. inv Hl. simpl. apply IHl1; auto. rewrite Ha,H2. easy.
  Qed.
End list.

(** ** Examples *)

Section Examples.
  Context `{HMonoid : Monoid}.
  Notation "0" := Azero : A_scope.
  Infix "+" := Aadd : A_scope.
  Infix "==" := Aeq : A_scope.

  Goal forall a b c d : A, 0 + a + 0 + (b + 0 + c) == a + (0 + b) + (c + 0).
  Proof. intros. monoid. Qed.
End Examples.


(* ######################################################################### *)
(** * Abelian monoid *)

(** ** Class *)
Class AMonoid {A} Aadd Azero Aeq := {
    amonoidMonoid :: @Monoid A Aadd Azero Aeq;
    amonoidComm :: Commutative Aadd Aeq;
    amonoidASGroup :: ASGroup Aadd Aeq
  }.

Coercion amonoidMonoid : AMonoid >-> Monoid.
(* Coercion amonoidComm : AMonoid >-> Commutative. *)
Coercion amonoidASGroup : AMonoid >-> ASGroup.

Arguments amonoidMonoid {A Aadd Azero Aeq}.
Arguments amonoidASGroup {A Aadd Azero Aeq}.

(** ** Theories *)

(* handle structures smaller than this *)
Ltac amonoid_smaller :=
  match goal with
  | M:Monoid ?op ?e ?aeq |- _ => monoid_core op e aeq
  | ASG:ASGroup ?op ?aeq |- _ => asgroup_core op aeq
  | SG:ASGroup ?op ?aeq |- _ => sgroup_core op aeq
  end.

(* Simplify expressions on Abelian monoid <AM, op, e, aeq> *)
Ltac amonoid_core op e aeq :=
  repeat
    (try
       match goal with
       (* M + ASG，则顺序执行二者 *)
       | M:Monoid op e aeq, ASG:ASGroup op aeq |- _ =>
           monoid_core op e aeq; asgroup_core op aeq
       (* AM，则先转换为 M + ASG *)
       | AM:AMonoid op e aeq |- _ =>
           try pose proof (amonoidMonoid AM) as HMonoid;
           try pose proof (amonoidASGroup AM) as HASGroup
       end;
     try easy);
  amonoid_smaller.

(* Simplify expressions on Abelian monoid in current context *)
Ltac amonoid :=
  try match goal with AM:AMonoid ?op ?e ?aeq |- _ => amonoid_core op e aeq end;
  amonoid_smaller.

(** ** Instances *)

(** ** Examples *)
Section Examples.
  Context `{HAMonoid : AMonoid}.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Infix "==" := Aeq : A_scope.

  Goal forall a b c : A, a + (0 + b + c + 0) == 0 + c + (b + a + 0) + 0.
  Proof. amonoid. Qed.
End Examples.


(* ######################################################################### *)
(** * Group *)

(** ** Class *)
Class Group {A} Aadd Azero Aopp Aeq := {
    groupAoppProper :: Proper (Aeq ==> Aeq) Aopp;
    groupMonoid :: @Monoid A Aadd Azero Aeq;
    groupInvL :: InverseLeft Aadd Azero Aopp Aeq;
    groupInvR :: InverseRight Aadd Azero Aopp Aeq;
  }.
(* Coercion groupAoppProper : Group >-> Proper. *)
Coercion groupMonoid : Group >-> Monoid.
(* Coercion groupInvL : Group >-> InverseLeft. *)
(* Coercion groupInvR : Group >-> InverseRight. *)

Arguments groupMonoid {A Aadd Azero Aopp Aeq}.

(** ** Theories *)

(* Basic simplify on group <G, op, e, inv, aeq>, only for new features of group *)
Ltac group_basic_only op e inv aeq :=
  intros;
  repeat
    (try
       match goal with
       (* - a + a *)
       | [G:Group op e inv aeq, H:context[op (inv ?a) ?a] |-_] =>
           rewrite (inverseLeft a) in H at 1
       | [G:Group op e inv aeq |- context [op (inv ?a) ?a]] =>
           rewrite (inverseLeft a) at 1
       (* a + - a *)
       | [G:Group op e inv aeq, H:context[op ?a (inv ?a)] |-_] =>
           rewrite (inverseRight a) in H at 1
       | [G:Group op e inv aeq |- context [op ?a (inv ?a)]] =>
           rewrite (inverseRight a) at 1
       (* -a + (a + b) *)
       | [G:Group op e inv aeq, H:context[op (inv ?a) (op ?a ?b)] |- _] =>
           rewrite <- (associative (inv a) a) in H;
           rewrite (inverseLeft a) in H at 1
       | [G:Group op e inv aeq |- context[op (inv ?a) (op ?a ?b)] ] =>
           rewrite <- (associative (inv a) a);
           rewrite (inverseLeft a) at 1
       (* a + (-a + b) *)
       | [G:Group op e inv aeq, H:context[op ?a (op (inv ?a) ?b)] |- _] =>
           rewrite <- (associative a (inv a)) in H;
           rewrite (inverseRight a) in H at 1
       | [G:Group op e inv aeq |- context[op ?a (op (inv ?a) ?b)] ] =>
           rewrite <- (associative a (inv a));
           rewrite (inverseRight a) at 1
       (* (a + b) + -b *)
       | [G:Group op e inv aeq, H:context[op (op ?a ?b) (inv ?b)] |- _] =>
           rewrite (associative a b) in H;
           rewrite (inverseRight b) in H at 1
       | [G:Group op e inv aeq |- context[op (op ?a ?b) (inv ?b)] ] =>
           rewrite (associative a b);
           rewrite (inverseRight b) at 1
       (* (a + -b) + b *)
       | [G:Group op e inv aeq, H:context[op (op ?a (inv ?b)) ?b] |- _] =>
           rewrite (associative a (inv b)) in H;
           rewrite (inverseLeft b) in H at 1
       | [G:Group op e inv aeq |- context[op (op ?a (inv ?b)) ?b] ] =>
           rewrite (associative a (inv b));
           rewrite (inverseLeft b) at 1
       end;
     try easy).

(* handle structures smaller than this *)
Ltac group_smaller :=
  match goal with
  | AM : AMonoid ?op ?e ?aeq |- _ => amonoid_core op e aeq
  | M:Monoid ?op ?e ?aeq |- _ => monoid_core op e aeq
  | ASG:ASGroup ?op ?aeq |- _ => asgroup_core op aeq
  | SG:ASGroup ?op ?aeq |- _ => sgroup_core op aeq
  end.

(* Basic simplify on group <G, op, e, inv, aeq> *)
Ltac group_basic_core op e inv aeq :=
  repeat
    (try
       match goal with
       (* G + M，则顺序执行二者 *)
       | G:Group ?op ?e ?inv ?aeq, M:Monoid ?op ?e ?aeq |- _ =>
           group_basic_only op e inv aeq;
           monoid_core op e aeq
       (* G，则转换为 G + M *)
       | G:Group ?op ?e ?inv ?aeq |- _ => try pose proof (groupMonoid G) as HMonoid
       end;
     try easy);
  group_smaller.

(* Basic simplify on group in current context *)
Ltac group_basic :=
  try match goal with
      G:Group ?op ?e ?inv ?aeq |- _ => group_basic_core op e inv aeq
    end;
  group_smaller.

Section test.
  Context `{HGroup : Group}.
  Notation "0" := Azero : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "==" := Aeq : A_scope.

  (* `group_basic` can finish "monoid" tasks *)
  Goal forall a b c : A, a + 0 == 0 + a -> (a + b) + 0 + c == 0 + a + 0 + (b + 0 + c).
  Proof. group_basic. Qed.

  (* `group_basic` can do `group inv` tasks *)
  Goal forall a b c d e : A, c + -c + - d + d == e -> - a + a + b + - b == e.
  Proof. group_basic. Qed.

  (* group inverse with associativity *)
  Goal forall a b : A, -a + (a + b) == b.
  Proof. group_basic. Qed.
End test.

(*
  More properties on Group

  1.  Arkansas Aech University / Dr. Marcel B. Finan /
      MATH 4033: Elementary Modern Algebra
  
  (a) 5 Definition and Examples of Groups
  https://faculty.atu.edu/mfinan/4033/absalg5.pdf
  (b) 14 Elementary Properties of Groups
  https://faculty.atu.edu/mfinan/4033/absalg14.pdf
 *)
Section GroupTheory.
  
  Context `{HGroup : Group}.
  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.

  (** *** my added lemmas (part 1) *)
  
  (** - 0 == 0 *)
  Theorem group_opp_0 : - 0 == 0.
  Proof.
    (* -e == -e + e == e *)
    pose proof (inverseLeft 0). rewrite identityRight in H. auto.
  Qed.

  (** *** lemmas from textbook *)
  
  (* Theorem 5.1 *)
  
  (** left identity element is unique  *)
  Theorem group_id_uniq_l : forall e',
      (forall a, e' + a == a) -> e' == 0.
  Proof.
    (* e == e' + e == e' *)
    intros. rewrite <- (H 0). group_basic.
  Qed.

  (** right identity element is unique  *)
  Theorem group_id_uniq_r : forall e', (forall a, a + e' == a) -> e' == 0.
  Proof.
    (* e == e + e' == e' *)
    intros. rewrite <- (H 0). group_basic.
  Qed.

  (** left inverse element is unique *)
  Theorem group_opp_uniq_l : forall a b : A, a + b == 0 -> -a == b.
  Proof.
    (* -a == -a + 0 == -a + a + b == 0 + b == b *)
    intros.
    setoid_replace (-a) with (-a + 0) by group_basic. rewrite <- H. group_basic.
  Qed.
  
  (** right inverse element is unique *)
  Theorem group_opp_uniq_r : forall a b : A, a + b == 0 -> -b == a.
  Proof.
    (* -b == 0 + -b == a + b + b == a + 0 == a *)
    intros.
    setoid_replace (-b) with (0 + -b) by group_basic. rewrite <- H. group_basic.
  Qed.

  (* Theorem 14.1 *)
  (** c + a == c + b -> a == b *)
  Theorem group_cancel_l : forall a b c, c + a == c + b -> a == b.
  Proof.
    intros.
    (* a == 0+a == (-c+c)+a == (-c)+(c+a) == (-c)+(c+b) == (-c+c)+b == 0+b == b*)
    rewrite <- identityLeft at 1.
    setoid_replace 0 with (-c + c) by group_basic.
    rewrite associative. rewrite H. group_basic.
  Qed.

  (** a + c == b + c -> a == b *)
  Theorem group_cancel_r : forall a b c, a + c == b + c -> a == b.
  Proof.
    intros.
    (* a == a+0 == a+(c+ -c) == (a+c)+(-c) == (b+c)+(-c) == b+(c+ -c) == b+0 == b *)
    rewrite <- identityRight at 1.
    setoid_replace 0 with (c + -c) by group_basic.
    rewrite <- associative. rewrite H. group_basic.
  Qed.
  
  (** - - a == a *)
  Theorem group_opp_opp : forall a,  - - a == a.
  Proof. intros. apply group_cancel_l with (- a). group_basic. Qed.

  (** a - a == 0 *)
  Theorem group_sub_self : forall a, a - a == 0.
  Proof. intros. group_basic. Qed.
    
  (** - a == - b -> a == b *)
  Lemma group_opp_inj : forall a b : A, - a == - b -> a == b.
  Proof.
    intros. rewrite <- group_opp_opp. rewrite H. rewrite group_opp_opp. easy.
  Qed.

  (** - (a + b) == (- b) + (- a) *)
  Theorem group_opp_distr : forall a b, - (a + b) == (- b) + (- a).
  Proof.
    intros.
    (* (a+b) + -(a+b) == 0 == a + -a == a + 0 + -a == a + (b + -b) + -a
      == (a + b) + (-b + -a), by cancel_l, got it *)
    apply group_cancel_l with (a + b).
    rewrite inverseRight. rewrite <- associative. rewrite (associative a b).
    group_basic.
  Qed.

  (** - a == 0 <-> a == 0 *)
  Lemma group_opp_eq0_iff : forall a : A, - a == 0 <-> a == 0.
  Proof.
    intros. split; intros.
    - apply group_cancel_l with (-a). group_basic.
    - rewrite H. rewrite group_opp_0. easy.
  Qed.

  (** - a <> 0 <-> a <> 0 *)
  Lemma group_opp_neq0_iff : forall a : A, ~(- a == 0) <-> ~(a == 0).
  Proof. intros. rewrite group_opp_eq0_iff. easy. Qed.
    
  (* Theorem 14.2 *)
  (** a + b == c -> a == c + (-b) *)
  Theorem group_sol_l : forall a b c, a + b == c -> a == c + (- b).
  Proof. intros. apply group_cancel_r with (b). rewrite H. group_basic. Qed.

  (** a + b == c -> b == (-a) + c *)
  Theorem group_sol_r : forall a b c, a + b == c -> b == (- a) + c.
  Proof. intros. apply group_cancel_l with (a). rewrite H. group_basic. Qed.

  (** a - b == 0 <-> a == b *)
  Theorem group_sub_eq0_iff_eq : forall a b, a - b == 0 <-> a == b.
  Proof.
    intros. split; intros.
    - apply group_cancel_r with (-b). group_basic.
    - rewrite H. group_basic.
  Qed.

  (* This theorem will be moved to ListExt, because this dependends list theory *)
  (** Theorem 14.3 (Generalized Associative Law) *)
  (* Section th14_3. *)
  (*   Notation "'\sum' a '&' l " := (fold_left Aadd l a) (at level 10). *)
    
  (*   Theorem group_assoc_general : forall (l1 l2 : list A), *)
  (*     \sum 0 & l1 + \sum 0 & l2 == \sum 0 & (l1 ++ l2). *)
  (*   Proof. *)
  (*     induction l1, l2; simpl; group_basic. *)
  (*     - rewrite app_nil_r. easy. *)
  (*     - Search fold_left. *)
  (*       ? rebase *)

          
  (*     -  *)
  (*       (* H1. forall a l1 l2, Σ a & (l1 ++ l2) == Σ (Σ a & l1) & l2 *)
  (*          H2. forall a b l, a + Σ b & l == Σ (a + b) & l *)
  (*          H3. forall a b l, Σ a & (b :: l) == Σ (a + b) & l *)
  (*          by H1, right == Σ (Σ a1 & l1) & (a2 :: l2). *)
  (*          by H2, left  == Σ ((Σ a1 & l1) + a2) & l2). *)
  (*          remember (Σ a1 & l1) as c, then goal become to *)
  (*             Σ (c + a2) & l2 == Σ c & (a2 :: l2) *)
  (*          by H3, we got it. *) *)
  (*       assert (forall a l1 l2, Σ a & (l1 ++ l2) == Σ (Σ a & l1) & l2) as H1. *)
  (*       { intros a l0. revert a. induction l0; intros; try easy. *)
  (*         simpl. rewrite IHl0. easy. } *)
  (*       assert (forall a b l, a + Σ b & l == Σ (a + b) & l) as H2. *)
  (*       { intros. revert a b. induction l; simpl; intros; try easy. *)
  (*         simpl. rewrite IHl. *)
  (*         (** fold_left preveres the aeq *) *)
  (*         assert (forall l a1 a2, a1 == a2 -> Σ a1 & l == Σ a2 & l). *)
  (*         { induction l0; intros; simpl in *; auto. *)
  (*           apply IHl0. rewrite H. easy. } *)
  (*         apply H. group_basic. } *)
  (*       assert (forall a b l, Σ a & (b :: l) == Σ (a + b) & l) as H3. *)
  (*       { intros. revert a b. induction l; try easy. } *)
  (*       rewrite H1. rewrite H2. rewrite H3. easy. *)
  (*   Qed. *)
  (* End th14_3. *)

  Section th14_4.

    Import ZArith.

    (** Definition 14.2 (power)
      a ^ 0      == e
      a ^ n      == a ^ (n-1) * a, for n >= 1
      a ^ (-n)   == (-a) ^ n,  for n >= 1
     *)
    Definition group_power (a : A) (n : Z) : A :=
      match n with
      | Z0 => 0
      | Zpos m => iterate (fun x => Aadd x a) (Pos.to_nat m) 0
      | Z.neg m => iterate (fun x => Aadd x (Aopp a)) (Pos.to_nat m) 0
      end.
    Infix "^" := group_power.
    
    Section test.
      Variable (a1 a2 a3 a4 : A).
      (* Compute group_power a1 3. *)
      (* Compute group_power a1 (-3). *)

    End test.

    (** Remark 14.2 *)
    Lemma group_power_eq1 (n : Z) :
      match n with
      | Z0 => forall a, a ^ n == 0
      | Zpos m => forall a, a ^ n == fold_left Aadd (repeat a (Z.to_nat n)) 0
      | Zneg m => forall a, a ^ n == fold_left Aadd (repeat (-a) (Z.to_nat (-n))) 0
      end.
    Proof.
      destruct n; intros; auto.
    Abort.

    (** Theorem 14.4 *)
    Theorem group_power_inv : forall a n, (a^n) + (a^(- n)) == 0.
    Abort.

    Theorem group_power_plus : forall a m n, (a^m) + (a^n) == a^(m+n).
    Abort.

    Theorem group_power_mul : forall a m n, (a^m)^n == a^(m*n).
    Abort.

  End th14_4.

  
  (** *** my added lemmas (part 2) *)

  (* b == 0 -> a + b == a *)
  Lemma group_add_eq_l : forall a b : A, b == 0 -> a + b == a.
  Proof. intros. rewrite H. apply identityRight. Qed.

  (* a == 0 -> a + b == b *)
  Lemma group_add_eq_r : forall a b : A, a == 0 -> a + b == b.
  Proof. intros. rewrite H. apply identityLeft. Qed.

  (* a + b == a -> b == 0 *)
  Lemma group_add_eq_l_inv : forall a b : A, a + b == a -> b == 0.
  Proof.
    intros.
    assert (a + b == a + 0). rewrite H. group_basic.
    apply group_cancel_l in H0. auto.
  Qed.

  (* a + b == b -> a == 0 *)
  Lemma group_add_eq_r_inv : forall a b : A, a + b == b -> a == 0.
  Proof.
    intros. assert (a + b == 0 + b). rewrite H. group_basic.
    apply group_cancel_r in H0. auto.
  Qed.

  (* - a == b -> a == - b *)
  Lemma group_opp_exchg_l : forall a b : A, - a == b -> a == - b.
  Proof. intros. rewrite <- H. rewrite group_opp_opp. easy. Qed.

  (* a == - b -> - a == b *)
  Lemma group_opp_exchg_r : forall a b : A, a == - b -> - a == b.
  Proof. intros. rewrite H. rewrite group_opp_opp. easy. Qed.

End GroupTheory.

(* Simplfy expressions on group <G, op, e, inv, aeq>, using advanced properties *)
Ltac group_advanced_only op e inv aeq :=
  intros;
  repeat
    (try
       match goal with
       (* ------------ simplify in both context and goal ------------ *)
       (* - 0 *)
       | [G:Group op e inv aeq, H:context [inv e] |- _] =>
           rewrite group_opp_0 in H at 1
       | [G:Group op e inv aeq |- context [inv e]] =>
           rewrite group_opp_0 at 1
       (* - - a *)
       | [G:Group op e inv aeq, H:context [inv (inv ?a)] |- _] =>
           rewrite (group_opp_opp a) in H
       | [G:Group op e inv aeq |- context [inv (inv ?a)]] =>
           rewrite (group_opp_opp a)
       (* - (a + b) *)
       | [G:Group op e inv aeq, H:context [inv (op ?a ?b)] |- _] =>
           rewrite (group_opp_distr a b) in H at 1
       | [G:Group op e inv aeq |- context [inv (op ?a ?b)]] =>
           rewrite (group_opp_distr a b) at 1
       (* - a == - b  *)
       | [G:Group op e inv aeq, H:context [aeq (inv ?a) (inv ?b)] |- _] =>
           apply group_opp_inj in H
       | [G:Group op e inv aeq |- context [aeq (inv ?a) (inv ?b)]] =>
           apply group_opp_inj
       (* - a == 0 *)
       | [G:Group op e inv aeq, H:context [aeq (inv ?a) e] |- _] =>
           rewrite (group_opp_eq0_iff a) in H
       | [G:Group op e inv aeq |- context [aeq (inv ?a) e]] =>
           rewrite (group_opp_eq0_iff a)
       (* a + b == a *)
       | [G:Group op e inv aeq, H: aeq (op ?a ?b) ?a |- _] =>
           apply group_add_eq_l_inv in H
       | [G:Group op e inv aeq |- aeq (op ?a ?b) ?a] =>
           apply group_add_eq_l
       (* a == a + b *)
       | [G:Group op e inv aeq, H: aeq ?a (op ?a ?b) |- _] =>
           symmetry in H; apply group_add_eq_l_inv in H
       | [G:Group op e inv aeq |- aeq ?a (op ?a ?b)] =>
           symmetry; apply group_add_eq_l
       (* a + b == b *)
       | [G:Group op e inv aeq, H: aeq (op ?a ?b) ?b |- _] =>
           apply group_add_eq_r_inv in H
       | [G:Group op e inv aeq |- aeq (op ?a ?b) ?b] =>
           apply group_add_eq_r
       (* b == a + b *)
       | [G:Group op e inv aeq, H: aeq ?b (op ?a ?b) |- _] =>
           symmetry in H; apply group_add_eq_r_inv in H
       | [G:Group op e inv aeq |- aeq ?b (op ?a ?b)] =>
           symmetry; apply group_add_eq_r
       (* (a + b) + c == a *)
       | [G:Group op e inv aeq, H: aeq (?op (?op ?a ?b) ?c) ?a |- _] =>
           rewrite (associative a b c) in H; apply group_add_eq_l_inv in H
       | [G:Group op e inv aeq |- aeq (?op (?op ?a ?b) ?c) ?a] =>
           rewrite (associative a b c); apply group_add_eq_l
       (* a == (a + b) + c *)
       | [G:Group op e inv aeq, H: aeq ?a (?op (?op ?a ?b) ?c) |- _] =>
           symmetry in H;
           rewrite (associative a b c) in H; apply group_add_eq_l_inv in H
       | [G:Group op e inv aeq |- aeq ?a (?op (?op ?a ?b) ?c)] =>
           symmetry; rewrite (associative a b c); apply group_add_eq_l
       (* (a + b) + c == b, need commutative *)
       (* b == (a + b) + c, need commutative *)
       (* Deeper pattern matching is not currently provided *)

       (* ------------ simplify in goal only ------------ *)
       (* - a == b |- a == - b *)
       | [G:Group op e inv aeq, H:context [aeq (inv ?a) ?b] |- aeq ?a (inv ?b)] =>
           apply group_opp_exchg_l
       (* a == - b |- - a == b *)
       | [G:Group op e inv aeq, H:context [aeq ?a (inv ?b)] |- aeq (inv ?a) ?b] =>
           apply group_opp_exchg_r
       end;
     try easy).

(* Simplfy expressions on group <G, op, e, inv, aeq> *)
Ltac group_core op e inv aeq :=
  try group_advanced_only op e inv aeq;
  try group_basic. (* it will also call `group_smaller` *)
  
(* Simplfy expressions on group in current context *)
Ltac group :=
  try match goal with G:Group ?op ?e ?inv ?aeq |- _ => group_core op e inv aeq end;
  group_smaller.


(* (** ** Instances *) *)
(* Section Instances. *)

(*   Import Qcanon Reals. *)
  
(*   #[export] Instance Qc_add_Group : Group Qcplus 0 Qcopp. *)
(*   split_intro; subst; ring. Qed. *)

(*   #[export] Instance R_add_Group : Group Rplus 0%R Ropp. *)
(*   split_intro; subst; ring. Qed. *)

(* End Instances. *)

(** ** Examples *)
Section Examples.

  Context `{HGroup : Group}.
  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.

  Goal forall a b : A, b == 0 -> a + b == a.
  Proof. group. Qed.

  Goal forall a b : A, a == 0 -> a + b == b.
  Proof. group. Qed.

  Goal forall a b : A, a + b == b -> a == 0.
  Proof. group. Qed.

  Goal forall a b : A, a + b == a -> b == 0.
  Proof. group. Qed.

  Goal forall a b : A, a == - b -> - a == b.
  Proof. group. Qed.
  
  Goal forall a b : A, - a == b -> a == - b.
  Proof. group. Qed.
         
  Goal forall a b c d : A, - (a + 0 + (b - c)) + (- - d + 0) == c - b + - (- d + a).
  Proof. group. Qed.
  
End Examples.


(* ######################################################################### *)
(** * Abelian Group *)

(** ** Class *)
Class AGroup {A} Aadd Azero Aopp Aeq := {
    agroupGroup :: @Group A Aadd Azero Aopp Aeq;
    agroupComm :: Commutative Aadd Aeq;
    agroupAM :: AMonoid Aadd Azero Aeq;
  }.
Coercion agroupGroup : AGroup >-> Group.
(* Coercion agroupComm : AGroup >-> Commutative. *)
Coercion agroupAM : AGroup >-> AMonoid.

Arguments agroupGroup {A Aadd Azero Aopp Aeq}.
Arguments agroupAM {A Aadd Azero Aopp Aeq}.

(** ** Theories *)
Section Theory.
  
  Context `{HAGroup : AGroup}.
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Notation "a - b" := (a + (-b)).

  (* (** a - b == - (b - a) *) *)
  (* Lemma agroup_sub_comm : forall a b, a - b == - (b - a). *)
  (* Proof. *)
  (*   intros. rewrite group_opp_distr. rewrite group_opp_opp. easy. *)
  (* Qed. *)

  (* (** - (a + b) == -a + (-b) *) *)
  (* Lemma agroup_sub_distr : forall a b, - (a + b) == -a + (-b). *)
  (* Proof. *)
  (*   intros. rewrite group_opp_distr. apply commutative. *)
  (* Qed. *)

  (* (** (a - b) - c == (a - c) - b *) *)
  (* Lemma agroup_sub_perm : forall a b c, (a - b) - c == (a - c) - b. *)
  (* Proof. *)
  (*   intros. rewrite ?associative. rewrite (commutative (-b)). easy. *)
  (* Qed. *)

  (* (** (a - b) - c == a - (b + c) *) *)
  (* Lemma agroup_sub_assoc : forall a b c, (a - b) - c == a - (b + c). *)
  (* Proof. *)
  (*   intros. rewrite ?associative. rewrite agroup_sub_distr. easy. *)
  (* Qed. *)
  
End Theory.


(* handle structures smaller than this *)
Ltac agroup_smaller :=
  match goal with
  | G:Group ?op ?e ?inv ?aeq |- _ => group_core op e inv aeq
  | AM:AMonoid ?op ?e ?aeq |- _ => amonoid_core op e aeq
  | M:Monoid ?op ?e ?aeq |- _ => monoid_core op e aeq
  | ASG:ASGroup ?op ?aeq |- _ => asgroup_core op aeq
  | SG:ASGroup ?op ?aeq |- _ => sgroup_core op aeq
  end.

(* Simplify expressions on Abelian group <op, e, inv, aeq> *)
Ltac agroup_core op e inv aeq :=
  repeat
    (try
       match goal with
       (* G + AM，则顺序执行二者 *)
       | G:Group op e inv aeq, AM:AMonoid op e aeq |- _ =>
           group_core op e inv aeq; amonoid_core op e aeq
       (* AG，则先转换为 G + AM *)
       | AG:AGroup op e inv aeq |- _ =>
           try pose proof (agroupGroup AG) as HGroup;
           try pose proof (agroupAM AG) as HAMonoid
       end;
     try easy);
  agroup_smaller.

(* Simplify expressions on Abelian group in current context *)
Ltac agroup :=
  try match goal with AG:AGroup ?op ?e ?inv ?aeq |- _ => agroup_core op e inv aeq end;
  agroup_smaller.

(** ** Instances *)
(* Section Instances. *)

(*   Import Qcanon Reals. *)
  
(*   #[export] Instance Qc_add_AGroup : AGroup Qcplus 0 Qcopp. *)
(*   split_intro; subst; ring. Qed. *)

(*   #[export] Instance R_add_AGroup : AGroup Rplus 0%R Ropp. *)
(*   split_intro; subst; ring. Qed. *)

(* End Instances. *)

(** ** Examples *)
Section Examples.
  Context `{HAGroup : AGroup}.
  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "-" := Asub : A_scope.

  Goal forall a b c : A, ((a - b) - c == a - (b + c)).
  Proof. agroup. Qed.

  Goal forall a b c d : A, - (a + 0 + (b - c)) + (- - d + 0) == - (- d + a) - b + c.
  Proof. agroup. Qed.

End Examples.


(* ######################################################################### *)
(** * SemiRing *)
(* 区分半环与环：半环加法不需要逆元。比如<nat,+,*>是半环，但不是环 *)

(** ** Class *)

Class SRing {A} Aadd Azero Amul Aone Aeq := {
    sringAddAM :: @AMonoid A Aadd Azero Aeq; (* 不确定交换性是否必要，姑且先留下 *)
    sringMulAM :: AMonoid Amul Aone Aeq; (* 不确定交换性是否必要，姑且先留下 *)
    sringDistrL :: DistrLeft Aadd Amul Aeq;
    sringDistrR :: DistrRight Aadd Amul Aeq;
  }.
Coercion sringAddAM : SRing >-> AMonoid.
Coercion sringMulAM : SRing >-> AMonoid.
(* Coercion sringDistrL : SRing >-> DistrLeft. *)
(* Coercion sringDistrR : SRing >-> DistrRight. *)

(** ** Theories *)

(** ** Instances *)
(* Section Instances. *)

(*   Import Nat ZArith Qcanon Reals. *)

(*   #[export] Instance nat_SRing : SRing Nat.add 0%nat Nat.mul 1%nat. *)
(*   repeat constructor; intros; ring. Qed. *)
  
(*   #[export] Instance Z_SRing : SRing Z.add 0%Z Z.mul 1%Z. *)
(*   repeat constructor; intros; ring. Qed. *)
  
(*   #[export] Instance Qc_SRing : SRing Qcplus 0 Qcmult 1. *)
(*   repeat constructor; intros; ring. Qed. *)

(*   #[export] Instance R_SRing : SRing Rplus R0 Rmult R1. *)
(*   split_intro; subst; ring. Qed. *)

(* End Instances. *)

(** ** Examples *)


(* ######################################################################### *)
(** * Ring *)

(** ** Class *)

(* Note that, the ring theory in mathematics needn't commutative for `mul` operation,
   but ring theory in Coq need it.
   We will distinguish ring and abelian ring with class name Ring and ARing.  *)

Class Ring {A} Aadd Azero Aopp Amul Aone Aeq := {
    ringAddAG :: @AGroup A Aadd Azero Aopp Aeq;
    ringMulM :: Monoid Amul Aone Aeq;
    ringDistrL :: DistrLeft Aadd Amul Aeq;
    ringDistrR :: DistrRight Aadd Amul Aeq;
  }.
Coercion ringAddAG : Ring >-> AGroup.
Coercion ringMulM : Ring >-> Monoid.
(* Coercion ringDistrL : Ring >-> DistrLeft. *)
(* Coercion ringDistrR : Ring >-> DistrRight. *)

Arguments ringAddAG {A Aadd Azero Aopp Amul Aone Aeq}.

(** ** Theories *)
Section Theory.

  Context `{HRing : Ring}.

  Infix "+" := Aadd : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + -b).
  Infix "*" := Amul : A_scope.

End Theory.

(** ** Instances *)
(* Section Instances. *)

(*   Import ZArith Qcanon Reals. *)

(*   #[export] Instance Z_Ring : Ring Z.add 0%Z Z.opp Z.mul 1%Z. *)
(*   repeat constructor; intros; ring. Qed. *)
  
(*   #[export] Instance Qc_Ring : Ring Qcplus 0 Qcopp Qcmult 1. *)
(*   repeat constructor; intros; ring. Qed. *)

(*   #[export] Instance R_Ring : Ring Rplus R0 Ropp Rmult R1. *)
(*   repeat constructor; intros; ring. Qed. *)

(* End Instances. *)

(** ** Examples *)

(* Section Examples. *)

(*   Import Reals. *)
(*   Open Scope R_scope. *)
  
(*   Goal forall a b c : R, a * (b + c) = a * b + a * c. *)
(*   Proof. apply distrLeft. Qed. *)

(* End Examples. *)
  

(* ######################################################################### *)
(** * Abelian ring *)

(** ** Class *)

Class ARing {A} Aadd Azero Aopp Amul Aone Aeq := {
    aringRing :: @Ring A Aadd Azero Aopp Amul Aone Aeq;
    aringMulComm :: Commutative Amul Aeq;
    aringMulAM :: AMonoid Amul Aone Aeq;
  }.
Coercion aringRing : ARing >-> Ring.
(* Coercion aringMulComm : ARing >-> Commutative. *)
Coercion aringMulAM : ARing >-> AMonoid.

(** ** Theories *)

Lemma make_ring_theory `(HARing : ARing)
  : ring_theory Azero Aone Aadd Amul (fun x y => Aadd x (Aopp y)) Aopp Aeq.
Proof.
  constructor; intros;
    try (rewrite ?identityLeft,?associative; reflexivity);
    try (rewrite commutative; reflexivity).
  rewrite distrRight; reflexivity.
  rewrite inverseRight; reflexivity.
Qed.

Section Theory.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).
  Infix "==" := Aeq.
  Infix "+" := Aadd.
  Notation "0" := Azero.
  Notation "- a" := (Aopp a).
  Notation Asub a b := (a + -b).
  Infix "*" := Amul.

  (** a * 0 == 0 *)
  (* a*0 + 0 == a*0 == a*(0+0) == a*0 + a*0，then cancellation *)
  Lemma ring_mul_0_r : forall a : A, a * 0 == 0.
  Proof. intros. ring. Qed.

  (** 0 * a == 0 *)
  Lemma ring_mul_0_l : forall a : A, 0 * a == 0.
  Proof. intros. ring. Qed.

  (** a * a == 1, then a == 1 or a == -1 *)
  (* Tips: I can't prove it now..., and this is used in `OrthogonalMatrix` *)
  Lemma ring_sqr_eq1_imply_1_neg1 : forall (a : A),
      a * a == Aone -> a == Aone \/ a == (- Aone).
  Proof.
  Admitted.

  (** (- a) * b == - (a * b) *)
  (* a*b + (-a)*b = 0*b = 0, thus, -(a*b) = (-a)*b *)
  Lemma ring_mul_opp_l : forall a b, (- a) * b == - (a * b).
  Proof. intros. ring. Qed.

  (** a * (- b) == - (a * b) *)
  Lemma ring_mul_opp_r : forall a b, a * (- b) == - (a * b).
  Proof. intros. ring. Qed.
    
  (** (- a) * (- b) == a * b *)
  (* (-a)*(-b)= - a*(-b) = - - (a*b) = a*b *)
  Lemma ring_mul_opp_opp : forall a b, (- a) * (- b) == a * b.
  Proof. intros. ring. Qed.
  
End Theory.

(* (** ** Instances *) *)
(* Section Instances. *)

(*   Import ZArith Qcanon Reals. *)

(*   #[export] Instance Z_ARing : ARing Z.add 0%Z Z.opp Z.mul 1%Z. *)
(*   repeat constructor; intros; ring. Qed. *)
  
(*   #[export] Instance Ac_ARing : ARing Qcplus 0 Qcopp Qcmult 1. *)
(*   repeat constructor; intros; ring. Qed. *)

(* End Instances. *)

(** ** Examples *)

(* Example: abstract ring *)
Module Demo_abstract_ring.
  Context `{HARing : ARing}.
  Add Ring ring_inst : (make_ring_theory HARing).

  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope. Infix "*" := Amul : A_scope.
  Notation "0" := Azero : A_scope. Notation "1" := Aone : A_scope.

  Goal forall a b c : A, (a + b) * c == 0 + b * c * 1 + 0 + 1 * c * a.
  Proof. intros. ring. Qed.
End Demo_abstract_ring.

(** Example: a concrete ring *)
Module Demo_concrate_ring.
  (* A={Azero A1 A2 A3}. *)

  Inductive A := Azero | A1 | A2 | A3.
  Notation "0" := Azero. Notation "1" := A1. Notation "2" := A2. Notation "3" := A3.

  (* + 0 1 2 3
     0 0 1 2 3
     1 1 2 3 0
     2 2 3 0 1
     3 3 0 1 2 *)
  Definition add  (a b : A) :=
    match a,b with
    | 0,_ => b
    | 1,0 => 1 | 1,1 => 2 | 1,2 => 3 | 1,3 => 0
    | 2,0 => 2 | 2,1 => 3 | 2,2 => 0 | 2,3 => 1
    | 3,0 => 3 | 3,1 => 0 | 3,2 => 1 | 3,3 => 2
    end.
  Infix "+" := add.

  (* - 0 1 2 3
       0 3 2 1 *)
  Definition opp (a:A) :=
    match a with
    | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1
    end.
  Notation "- a" := (opp a).
  Notation "a - b" := (a + (-b)).

  (* * 0 1 2 3
     0 0 0 0 0
     1 0 1 2 3
     2 0 2 0 2
     3 0 3 2 1 *)
  Definition mul  (a b : A) :=
    match a,b with
    | 0,_ => 0
    | 1,_ => b
    | 2,0 => 0 | 2,1 => 2 | 2,2 => 0 | 2,3 => 2
    | 3,0 => 0 | 3,1 => 3 | 3,2 => 2 | 3,3 => 1
    end.
  Infix "*" := mul.

  Lemma add_comm : forall a b, a + b = b + a.
  Proof. destruct a,b; auto. Qed.

  (* To get a ring structure in Coq, we must show ring_theory.
     Now, there are two ways to finish it. *)

  (* Method 1: manual proof *)
  Lemma ring_thy : ring_theory 0 1 add mul (fun x y => add x (opp y)) opp eq.
  Proof.
    constructor; auto; intros;
      destruct x; auto; destruct y; auto; destruct z; auto.
  Qed.
  (* Add Ring ring_thy_inst1 : ring_thy. *)
  
  (* Method 2: first construct ARing structure, then use make_ring_theory *)
  Lemma ARing_inst : ARing add 0 opp mul 1 eq.
  Proof.
    repeat constructor; hnf; intros; hnf; intros;
      repeat match goal with a : A |- _ => destruct a; auto; try easy end.
  Qed.

  Add Ring ring_thy_inst2 : (make_ring_theory ARing_inst).

  Goal forall a b c : A, a + b + c - b = a + c.
  Proof. intros. ring. Qed.
  
End Demo_concrate_ring.


(* ######################################################################### *)
(** * Total order relations *)

(* ref : 
   https://en.wikipedia.org/wiki/Construction_of_the_real_numbers
   https://en.wikipedia.org/wiki/Partially_ordered_set
 *)
(* 
   Remark :
   1. The difference of total order relation and partial order relation is the 
      "total" propertity (forall a b, a <= b \/ b <= a).
   2. Four forms "<=, <, >, >=" are mutually derived. We will define "<" and "<="
      here, with the consistent law.
 *)

(** ** Class *)

(* Note, there are several ways to define {<, <=}
   1. first assume {<}, then define "a <= b := a < b \/ a = b"
   2. first assume {<=}, then define "a < b := a <= b /\ a <> b"
   3. assume {<,<=}, and assume "a <= b <-> a < b \/ a = b"

   We adopt the third way, to reduce the later definition work.
   i.e., given "Context `{Order}" is enough to declare {<, <=}, 
   thus the developer needn't and shouldn't to define another less-then relation,
   such as Qle, Rle etc. *)
Class Order {A} (Aeq Alt Ale : relation A) := {
    order_Aeq_equiv :: Equivalence Aeq;
    (* Alt is consistent with Aeq *)
    lt_aeq :: Proper (Aeq ==> Aeq ==> iff) Alt;
    (* Alt is anti-reflexivi *)
    lt_irrefl : forall a : A, ~ (Alt a a);
    (* Alt is anti-symmetric *)
    lt_antisym : forall a b : A, Alt a b -> Alt b a -> Aeq a b;
    (* Alt is transitive *)
    lt_trans : forall a b c : A, Alt a b -> Alt b c -> Alt a c;
    (* Alt three cases *)
    lt_cases : forall a b : A, {Alt a b} + {Alt b a} + {Aeq a b};
    
    (* Alt and Ale are consistent *)
    lt_le_cong : forall a b : A, Ale a b <-> (Alt a b \/ Aeq a b);
  }.

(** ** Theories *)

(** About "Aeq" *)
Section eq.
  Context `{HOrder : Order}.
  Infix "==" := Aeq.

  (** Aeq is decidable *)
  Lemma eq_dec : forall a b, {a == b} + {~(a == b)}.
  Proof.
    intros. destruct (lt_cases a b) as [[H1|H1]|H1]; auto.
    - right; intro. rewrite H in *. apply lt_irrefl in H1; auto.
    - right; intro. rewrite H in *. apply lt_irrefl in H1; auto.
  Defined.

  #[export] Instance eq_Dec : Dec Aeq.
  Proof. constructor. intro. apply eq_dec. Defined.

End eq.


(** About "Alt" *)
Section lt.
  Context `{HOrder : Order}.
  Infix "==" := Aeq.

  (* Note the sequence of the notations, the newer has higher priority than older *)
  Notation "a > b" := (Alt b a).
  Infix "<" := Alt.

  (** Lt is connected: a < b \/ b < a \/ a == b *)
  Lemma lt_connected : forall a b : A, Alt a b \/ Alt b a \/ a == b.
  Proof. intros. destruct (lt_cases a b) as [[H1|H1]|H1]; auto. Qed.

  (** a < b -> ~(a == b) *)
  Lemma lt_not_eq : forall a b : A, a < b -> ~(a == b).
  Proof. intros. intro. rewrite H0 in H. apply lt_irrefl in H; auto. Qed.
  
  (** Alt is decidable *)
  Lemma lt_dec : forall a b, {a < b} + {~(a < b)}.
  Proof.
    intros. destruct (lt_cases a b) as [[H1|H1]|H1]; auto.
    - right. intro. pose proof (lt_trans H1 H). apply lt_irrefl in H0; auto.
    - right. rewrite H1. apply lt_irrefl.
  Defined.

  #[export] Instance lt_Dec : Dec Alt.
  Proof. constructor. intro. apply lt_dec. Defined.

  (** a < b -> b < a -> False *)
  Lemma lt_gt_contr : forall a b : A, a < b -> b < a -> False.
  Proof.
    intros. apply lt_trans with (a:=a) in H0; auto. apply lt_irrefl in H0; auto.
  Qed.

  (** a < b -> ~(a == b) *)
  Lemma lt_imply_neq : forall a b : A, a < b -> ~(a == b).
  Proof. intros. intro. rewrite H0 in H. apply lt_irrefl in H. auto. Qed.
  
  (** a < b -> ~ (b < a) *)
  Lemma lt_not_lt : forall a b : A, a < b -> ~ (b < a).
  Proof. intros. intro. apply lt_gt_contr in H; auto. Qed.

End lt.


(** About "Ale" *)
Section le.
  Context `{HOrder : Order}.
  Infix "==" := Aeq.

  (* Note the sequence of the notations, the newer has higher priority than older *)
  Notation "a > b" := (Alt b a).
  Infix "<" := Alt.
  Notation "a >= b" := (Ale b a).
  Infix "<=" := Ale.

  (** Ale is consistent with Aeq  *)
  #[export] Instance le_aeq : Proper (Aeq ==> Aeq ==> iff) Ale.
  Proof.
    simp_proper; intros; split; intros.
    - apply lt_le_cong. apply lt_le_cong in H1. rewrite H,H0 in *. auto.
    - apply lt_le_cong. apply lt_le_cong in H1. rewrite H,H0 in *. auto.
  Qed.
  
  (** a < b -> a <= b *)
  Lemma le_if_lt : forall a b : A, a < b -> a <= b.
  Proof. intros. apply lt_le_cong. auto. Qed.
  
  (** a <= b -> b <= a -> a = b *)
  Lemma le_antisym : forall a b : A, a <= b -> b <= a -> a == b.
  Proof.
    intros. apply lt_le_cong in H, H0. destruct H, H0; subst; try easy.
    apply lt_antisym; auto.
  Qed.

  (** a <= a *)
  Lemma le_refl : forall a : A, a <= a.
  Proof. intros. apply lt_le_cong. right. easy. Qed.
  
  (* a <= b -> ~(a == b) -> a < b *)
  Lemma lt_if_le_and_neq : forall a b : A, a <= b -> ~(a == b) -> a < b.
  Proof. intros. apply lt_le_cong in H. destruct H; auto. easy. Qed.
  
  (** a <= b -> b <= c -> a <= c *)
  Lemma le_trans : forall a b c : A, a <= b -> b <= c -> a <= c.
  Proof.
    intros. apply lt_le_cong in H, H0. apply lt_le_cong. destruct H, H0.
    - left. apply lt_trans with b; auto.
    - rewrite H0 in H. left; auto.
    - rewrite <- H in H0. left; auto.
    - rewrite H0 in H. right; auto.
  Qed.
  
  (** a < b -> b <= c -> a < c *)
  Lemma lt_trans_lt_le : forall a b c : A, a < b -> b <= c -> a < c.
  Proof.
    intros. pose proof (le_if_lt H). pose proof (le_trans H1 H0).
    apply lt_if_le_and_neq; auto.
    intro. rewrite H3 in *. pose proof (le_antisym H0 H1). rewrite H4 in *.
    apply lt_irrefl in H; auto.
  Qed.
  
  (** a <= b -> b < c -> a < c *)
  Lemma lt_trans_le_lt : forall a b c : A, a <= b -> b < c -> a < c.
  Proof.
    intros. pose proof (le_if_lt H0). pose proof (le_trans H H1).
    apply lt_if_le_and_neq; auto.
    intro. rewrite H3 in *. pose proof (le_antisym H H1). rewrite H4 in *.
    apply lt_irrefl in H0; auto.
  Qed.
  
  (** a < b -> ~ (b <= a) *)
  (* Qclt_not_le: forall x y : Qc, x < y -> ~ y <= x *)
  Lemma lt_not_le : forall a b : A, a < b -> ~ (b <= a).
  Proof.
    intros. rewrite lt_le_cong. apply and_not_or. split.
    apply lt_not_lt; auto. intro. apply lt_not_eq in H; auto.
    rewrite H0 in H. destruct H; easy.
  Qed.
  
  (** ~ (a <= b) -> b < a *)
  (* Qcnot_le_lt: forall x y : Qc, ~ x <= y -> y < x *)
  Lemma not_le_lt : forall a b : A, ~ (a <= b) -> b < a.
  Proof.
    intros. rewrite lt_le_cong in H. apply not_or_and in H. destruct H.
    destruct (lt_cases a b) as [[H1|H1]|H1]; try easy.
  Qed.
  
  (** a <= b -> ~ (b < a) *)
  Lemma le_not_lt : forall a b : A, a <= b -> ~ (b < a).
  Proof.
    intros. rewrite lt_le_cong in H. destruct H.
    apply lt_not_lt; auto. rewrite H in *. apply lt_irrefl.
  Qed.
  
  (** ~ (a < b) -> b <= a *)
  Lemma not_lt_le : forall a b : A, ~ (a < b) -> b <= a.
  Proof.
    intros. apply lt_le_cong.
    destruct (lt_cases a b) as [[H1|H1]|H1]; auto; try easy.
    right. symmetry; auto.
  Qed.

  (** a <= b -> b <= a -> a == b *)
  Lemma le_ge_eq : forall a b : A, a <= b -> b <= a -> a == b.
  Proof.
    intros. apply le_not_lt in H,H0.
    destruct (lt_cases a b) as [[H1|H1]|H1]; easy.
  Qed.

  (** {a <= b} + {~(a <= b)} *)
  Lemma le_dec : forall a b : A, {a <= b} + {~(a <= b)}.
  Proof.
    intros. destruct (lt_dec b a); auto.
    - right. apply lt_not_le; auto.
    - left. apply not_lt_le; auto.
  Qed.

  #[export] Instance le_Dec : Dec Ale.
  Proof. constructor; intros. apply le_dec. Qed.
  
  (** a <= b \/ b < a *)
  Lemma le_connected : forall a b : A, a <= b \/ b < a.
  Proof. intros. destruct (le_dec a b); auto. apply not_le_lt in n. auto. Qed.

End le.

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Abelian-ring with total order *)

Class OrderedARing {A} Aadd Azero Aopp Amul Aone Aeq Alt Ale := {
    or_ARing :: @ARing A Aadd Azero Aopp Amul Aone Aeq;
    or_Order :: Order Aeq Alt Ale;
    (* Lt is compatible with addition operation: a < b -> a + c < a + c *)
    lt_add_compat_r : forall a b c : A, Alt a b -> Alt (Aadd a c) (Aadd b c);
    (* Lt is compatible with opposition operation: a < b -> - b > - a *)
    lt_opp_compat : forall a b c : A, Alt a b -> Alt (Aopp b) (Aopp a);
    (* Lt is compatible with multiply operation: a < b -> 0 < c -> a * c < b * c *)
    lt_mul_compat_r : forall a b c : A,
      Alt a b -> Alt Azero c -> Alt (Amul a c) (Amul b c);
  }.
Coercion or_ARing : OrderedARing >-> ARing.
Coercion or_Order : OrderedARing >-> Order.

(** ** Theories *)

(** Properties for "lt" *)
Section theories.
  Context `{HOrderedARing : OrderedARing}.
  Add Ring ring_inst : (make_ring_theory or_ARing).

  Infix "==" := Aeq : A_scope.
  Infix "+" := Aadd : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub a b := (a + - b).
  Infix "-" := Asub : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "1" := Aone : A_scope.
  Notation "2" := (1 + 1) : A_scope.
  Notation "a ²" := (a * a) : A_scope.
  
  Notation "a > b" := (Alt b a) : A_scope.
  Notation "a >= b" := (Ale b a) : A_scope.
  Infix "<" := Alt : A_scope.
  Infix "<=" := Ale : A_scope.
  

  (** *** Properties for "lt" *)

  (** **** About "add" *)

  (* a < b -> c + a < c + b *)
  Lemma lt_add_compat_l : forall a b c : A, a < b -> c + a < c + b.
  Proof. intros. rewrite !(commutative c _). apply lt_add_compat_r; auto. Qed.
  
  (* a < b -> c < d -> a + c < b + d *)
  Lemma lt_add_compat : forall a b c d : A, a < b -> c < d -> a + c < b + d.
  Proof.
    intros. apply lt_trans with (a + d).
    apply lt_add_compat_l; auto. apply lt_add_compat_r; auto.
  Qed.

  (* c + a < c + b -> a < b *)
  Lemma lt_add_reg_l : forall a b c, c + a < c + b -> a < b.
  Proof.
    intros. apply lt_add_compat_l with (c:=-c) in H.
    rewrite <- !associative in H. rewrite inverseLeft in H.
    rewrite !identityLeft in H. auto.
  Qed.

  (* a + c < b + c -> a < b *)
  Lemma lt_add_reg_r : forall a b c, a + c < b + c -> a < b.
  Proof.
    intros.
    apply lt_add_compat_r with (c:=-c) in H.
    rewrite !associative in H. rewrite inverseRight in H.
    rewrite !identityRight in H. auto.
  Qed.
  
  (* a < b <-> - b < - a *)
  Lemma lt_opp_iff : forall a b : A, a < b <-> - b < - a.
  Proof.
    (* a < b <-> -b + a + -a < -b + b + -a <-> -b < -a *)
    intros. pose proof (ringAddAG HOrderedARing).
    split; intros.
    - apply lt_add_compat_l with (c:=-b) in H0.
      apply lt_add_compat_r with (c:=-a) in H0. agroup.
    - apply lt_add_reg_l with (c:=-b).
      apply lt_add_reg_r with (c:=-a). agroup.
  Qed.

  (* a < b <-> a - b < 0 *)
  Lemma lt_sub_iff : forall a b : A, a < b <-> a - b < 0.
  Proof.
    (* a < b <-> a + (- b) < b + (- b) -> a - b < 0 *)
    intros. pose proof (ringAddAG HOrderedARing).
    split; intros.
    - apply lt_add_reg_r with (c := b). agroup.
    - apply lt_add_compat_r with (c := b) in H0. agroup.
  Qed.

  (** a < 0 <-> 0 < - a *)
  Lemma lt0_iff_neg : forall a : A, a < 0 <-> 0 < - a.
  Proof. intros. rewrite lt_opp_iff. rewrite group_opp_0 at 1. easy. Qed.

  (** 0 < a <-> - a < 0 *)
  Lemma gt0_iff_neg : forall a : A, 0 < a <-> - a < 0.
  Proof. intros. rewrite lt_opp_iff. rewrite group_opp_0 at 1. easy. Qed.

  (** 0 < a -> 0 < b -> 0 < a + b *)
  Lemma add_gt0_if_gt0_gt0 : forall a b : A, 0 < a -> 0 < b -> 0 < a + b.
  Proof.
    intros. setoid_replace 0 with (0 + 0) by ring. apply lt_add_compat; auto.
  Qed.
    
  (** a < 0 -> b < 0 -> a + b < 0 *)
  Lemma add_lt0_if_lt0_lt0 : forall a b : A, a < 0 -> b < 0 -> a + b < 0.
  Proof.
    intros. setoid_replace 0 with (0 + 0) by ring. apply lt_add_compat; auto.
  Qed.
  
  (** a < 0 -> 0 < b -> a < b *)
  Lemma lt_if_lt0_gt0 : forall a b : A, a < 0 -> 0 < b -> a < b.
  Proof. intros. apply lt_trans with 0; auto. Qed.
  
  (** a <= 0 -> 0 < b -> a < b *)
  Lemma lt_if_le0_gt0 : forall a b : A, a <= 0 -> 0 < b -> a < b.
  Proof.
    intros. destruct (eq_dec a 0) as [H1|H1].
    - rewrite H1 in *. auto.
    - apply lt_trans with 0; auto. apply lt_le_cong in H. destruct H; easy.
  Qed.

  (** a < 0 -> 0 <= b -> a < b *)
  Lemma lt_if_lt0_ge0 : forall a b : A, a < 0 -> 0 <= b -> a < b.
  Proof.
    intros. destruct (eq_dec b 0) as [H1|H1].
    - rewrite H1 in *. auto.
    - apply lt_trans with 0; auto. apply lt_le_cong in H0. destruct H0; try easy.
      symmetry in H0. easy.
  Qed.

  (** a < 0 -> a < - a *)
  Lemma lt_neg_r_if_lt0 : forall a : A, a < 0 -> a < - a.
  Proof. intros. apply lt_if_lt0_gt0; auto. apply lt0_iff_neg; auto. Qed.

  (** 0 < a -> - a < a *)
  Lemma gt_neg_l_if_gt0 : forall a : A, 0 < a -> - a < a.
  Proof. intros. apply lt_if_lt0_gt0; auto. apply gt0_iff_neg; auto. Qed.

  
  (** **** About "mul" *)
  
  (* a < b -> 0 < c -> c * a < c * b *)
  Lemma lt_mul_compat_l : forall a b c : A, a < b -> 0 < c -> c * a < c * b.
  Proof. intros. rewrite !(commutative c _). apply lt_mul_compat_r; auto. Qed.

  (* a < b -> c < 0 -> c * b < c * a *)
  Lemma lt_mul_compat_l_neg : forall a b c : A, a < b -> c < 0 -> c * b < c * a.
  Proof.
    intros. apply lt_opp_iff in H0. rewrite group_opp_0 in H0.
    apply lt_opp_iff. ring_simplify. apply lt_mul_compat_l; auto.
  Qed.

  (* a < b -> c < 0 -> b * c < a * c *)
  Lemma lt_mul_compat_r_neg : forall a b c : A, a < b -> c < 0 -> b * c < a * c.
  Proof. intros. rewrite !(commutative _ c). apply lt_mul_compat_l_neg; auto. Qed.

  (** 0 < a -> 0 < b -> 0 < a * b *)
  Lemma mul_gt0_if_gt0_gt0 : forall a b : A, 0 < a -> 0 < b -> 0 < a * b.
  Proof.
    intros. setoid_replace 0 with (a * 0) by ring. apply lt_mul_compat_l; auto.
  Qed.
  
  (** a < 0 -> b < 0 -> 0 < a * b *)
  Lemma mul_gt0_if_lt0_lt0 : forall a b : A, a < 0 -> b < 0 -> 0 < a * b.
  Proof.
    intros. setoid_replace (a * b) with ((- a) * (- b)) by ring.
    apply mul_gt0_if_gt0_gt0. apply lt0_iff_neg; auto. apply lt0_iff_neg; auto.
  Qed.
  
  (** 0 < a -> b < 0 -> a * b < 0 *)
  Lemma mul_lt0_if_gt0_lt0 : forall a b : A, 0 < a -> b < 0 -> a * b < 0.
  Proof.
    intros. setoid_replace 0 with (a * 0) by ring. apply lt_mul_compat_l; auto.
  Qed.
  
  (** a < 0 -> 0 < b -> a * b < 0 *)
  Lemma mul_lt0_if_lt0_gt0 : forall a b : A, a < 0 -> 0 < b -> a * b < 0.
  Proof.
    intros. setoid_replace 0 with (0 * b) by ring. apply lt_mul_compat_r; auto.
  Qed.

  (** 0 < a * b -> 0 < a -> 0 < b *)
  Lemma gt0_mul_reg_gt0 : forall a b : A, 0 < a * b -> 0 < a -> 0 < b.
  Proof.
    intros. destruct (lt_cases 0 b) as [[H1|H1]|H1]; auto.
    - apply lt0_iff_neg in H1.
      pose proof (mul_gt0_if_gt0_gt0 H0 H1).
      setoid_replace (a * - b) with (- (a * b)) in H2 by ring.
      apply lt0_iff_neg in H2. apply lt_gt_contr in H; easy.
    - rewrite <- H1 in *. ring_simplify in H. apply lt_irrefl in H; easy.
  Qed.
  
  (** 0 < a * b -> a < 0 -> b < 0 *)
  Lemma gt0_mul_reg_lt0 : forall a b : A, 0 < a * b -> a < 0 -> b < 0.
  Proof.
    intros. setoid_replace (a * b) with ((- a) * (- b)) in H by ring.
    apply lt0_iff_neg. apply lt0_iff_neg in H0.
    apply (gt0_mul_reg_gt0 H) in H0; auto.
  Qed.
  
  
  (** *** Properties for "le" *)

  (** **** About "add" *)
  
  (** a <= b -> a + c <= a + c *)
  Lemma le_add_compat_r : forall a b c : A, a <= b -> a + c <= b + c.
  Proof.
    intros. apply lt_le_cong. apply lt_le_cong in H. destruct H.
    - left. apply lt_add_compat_r; auto.
    - right. rewrite H. easy.
  Qed.
  
  (** a <= b -> c + a <= c + b *)
  Lemma le_add_compat_l : forall a b c : A, a <= b -> c + a <= c + b.
  Proof. intros. rewrite !(commutative c _). apply le_add_compat_r; auto. Qed.
  
  (* a <= b -> c <= d -> a + c <= b + d *)
  Lemma le_add_compat : forall a b c d : A, a <= b -> c <= d -> a + c <= b + d.
  Proof.
    intros. apply le_trans with (a + d).
    apply le_add_compat_l; auto. apply le_add_compat_r; auto.
  Qed.

  (* c + a <= c + b -> a <= b *)
  Lemma le_add_reg_l : forall a b c, c + a <= c + b -> a <= b.
  Proof.
    intros. apply le_add_compat_l with (c:=-c) in H.
    rewrite <- !associative in H. rewrite inverseLeft in H.
    rewrite (identityLeft a) in H. rewrite (identityLeft b) in H. auto.
  Qed.

  (* a + c <= b + c -> a <= b *)
  Lemma le_add_reg_r : forall a b c, a + c <= b + c -> a <= b.
  Proof.
    intros. apply le_add_compat_r with (c:=-c) in H.
    rewrite !associative in H. rewrite inverseRight in H.
    rewrite (identityRight a) in H. rewrite (identityRight b) in H. auto.
  Qed.

  (** 0 <= a -> 0 <= b -> 0 <= a + b *)
  Lemma add_ge0_if_ge0_ge0 : forall a b : A, 0 <= a -> 0 <= b -> 0 <= a + b.
  Proof.
    intros. setoid_replace 0 with (0 + 0) by ring. apply le_add_compat; auto.
  Qed.
    
  (** a <= 0 -> b <= 0 -> a + b <= 0 *)
  Lemma add_le0_if_le0_le0 : forall a b : A, a <= 0 -> b <= 0 -> a + b <= 0.
  Proof.
    intros. setoid_replace 0 with (0 + 0) by ring. apply le_add_compat; auto.
  Qed.
  
  (* a <= b <-> - b <= - a *)
  Lemma le_opp_iff : forall a b : A, a <= b <-> - b <= - a.
  Proof.
    intros. rewrite !lt_le_cong. split; intros; destruct H.
    - left. apply lt_opp_iff in H; auto.
    - rewrite H. right. easy.
    - apply lt_opp_iff in H; auto.
    - apply group_opp_inj in H. right. easy.
  Qed.

  (** a <= 0 <-> 0 <= - a *)
  Lemma le0_iff_neg : forall a : A, a <= 0 <-> 0 <= - a.
  Proof. intros. rewrite le_opp_iff. rewrite group_opp_0 at 1. easy. Qed.

  (** 0 <= a <-> - a <= 0 *)
  Lemma ge0_iff_neg : forall a : A, 0 <= a <-> - a <= 0.
  Proof. intros. rewrite le_opp_iff. rewrite group_opp_0 at 1. easy. Qed.
  
  (** a <= 0 -> 0 <= b -> a <= b *)
  Lemma le_if_le0_ge0 : forall a b : A, a <= 0 -> 0 <= b -> a <= b.
  Proof. intros. apply le_trans with 0; auto. Qed.
  
  (** a < 0 -> 0 < b -> a <= b *)
  Lemma le_if_lt0_gt0 : forall a b : A, a < 0 -> 0 < b -> a <= b.
  Proof. intros. apply le_if_lt. apply lt_if_lt0_gt0; auto. Qed.
  
  (** a <= 0 -> 0 < b -> a <= b *)
  Lemma le_if_le0_gt0 : forall a b : A, a <= 0 -> 0 < b -> a <= b.
  Proof. intros. apply le_if_lt. apply lt_if_le0_gt0; auto. Qed.
  
  (** a < 0 -> 0 <= b -> a <= b *)
  Lemma le_if_lt0_ge0 : forall a b : A, a < 0 -> 0 <= b -> a <= b.
  Proof. intros. apply le_if_lt. apply lt_if_lt0_ge0; auto. Qed.

  (** a <= 0 -> a <= - a *)
  Lemma le_neg_r_if_le0 : forall a : A, a <= 0 -> a <= - a.
  Proof. intros. apply le_if_le0_ge0; auto. apply le0_iff_neg; auto. Qed.

  (** a < 0 -> a <= - a *)
  Lemma le_neg_r_if_lt0 : forall a : A, a < 0 -> a <= - a.
  Proof. intros. apply le_neg_r_if_le0. apply le_if_lt; auto. Qed.

  (** 0 <= a -> - a <= a *)
  Lemma ge_neg_l_if_ge0 : forall a : A, 0 <= a -> - a <= a.
  Proof. intros. apply le_if_le0_ge0; auto. apply ge0_iff_neg; auto. Qed.

  (** 0 < a -> - a <= a *)
  Lemma ge_neg_l_if_gt0 : forall a : A, 0 < a -> - a <= a.
  Proof. intros. apply ge_neg_l_if_ge0. apply le_if_lt; auto. Qed.

  
  (** **** About "mul" *)
  
  (** a <= b -> 0 <= c -> a * c <= b * c *)
  Lemma le_mul_compat_r : forall a b c : A, a <= b -> 0 <= c -> a * c <= b * c.
  Proof.
    intros. apply lt_le_cong. apply lt_le_cong in H, H0. destruct H,H0.
    - left. apply lt_mul_compat_r; auto.
    - right. rewrite <- H0. rewrite !ring_mul_0_r. easy.
    - right. rewrite H. easy.
    - right. rewrite H. easy.
  Qed.

  (** a <= b -> 0 <= c -> c * a <= c * b *)
  Lemma le_mul_compat_l : forall a b c : A, a <= b -> 0 <= c -> c * a <= c * b.
  Proof. intros. rewrite !(commutative c _). apply le_mul_compat_r; auto. Qed.

  (** a <= b -> c < 0 -> c * b <= c * a *)
  Lemma le_mul_compat_l_neg : forall a b c : A, a <= b -> c < 0 -> c * b <= c * a.
  Proof.
    intros. apply lt_le_cong in H. destruct H.
    - apply lt_mul_compat_l_neg with (c:=c) in H; auto. apply le_if_lt; auto.
    - rewrite H. apply le_refl.
  Qed.

  (** a <= b -> c < 0 -> b * c <= a * c *)
  Lemma le_mul_compat_r_neg : forall a b c : A, a <= b -> c < 0 -> b * c <= a * c.
  Proof. intros. rewrite !(commutative _ c). apply le_mul_compat_l_neg; auto. Qed.

  (** 0 <= a -> 0 <= b -> 0 <= a * b *)
  Lemma mul_ge0_if_ge0_ge0 : forall a b : A, 0 <= a -> 0 <= b -> 0 <= a * b.
  Proof.
    intros. setoid_replace 0 with (a * 0) by ring. apply le_mul_compat_l; auto.
  Qed.
  
  (** a <= 0 -> b <= 0 -> 0 <= a * b *)
  Lemma mul_ge0_if_le0_le0 : forall a b : A, a <= 0 -> b <= 0 -> 0 <= a * b.
  Proof.
    intros. setoid_replace (a * b) with ((- a) * (- b)) by ring.
    apply mul_ge0_if_ge0_ge0. apply le0_iff_neg; auto. apply le0_iff_neg; auto.
  Qed.
    
  (** 0 <= a -> b <= 0 -> a * b <= 0 *)
  Lemma mul_le0_if_ge0_le0 : forall a b : A, 0 <= a -> b <= 0 -> a * b <= 0.
  Proof.
    intros. setoid_replace 0 with (a * 0) by ring. apply le_mul_compat_l; auto.
  Qed.

  (** a <= 0 -> 0 <= b -> a * b <= 0 *)
  Lemma mul_le0_if_le0_ge0 : forall a b : A, a <= 0 -> 0 <= b -> a * b <= 0.
  Proof.
    intros. setoid_replace 0 with (0 * b) by ring. apply le_mul_compat_r; auto.
  Qed.

  (** 0 <= a * b -> 0 < a -> 0 <= b *)
  Lemma ge0_mul_reg_ge0 : forall a b : A, 0 <= a * b -> 0 < a -> 0 <= b.
  Proof.
    intros. destruct (le_dec 0 b) as [H1|H1]; auto.
    destruct (eq_dec b 0) as [H2|H2].
    - rewrite H2 in *. apply le_refl.
    - exfalso. apply not_le_lt in H1.
      pose proof (mul_lt0_if_gt0_lt0 H0 H1).
      apply lt_not_le in H3. easy.
  Qed.
  
  (** 0 <= a * b -> a < 0 -> b <= 0 *)
  Lemma ge0_mul_reg_le0 : forall a b : A, 0 <= a * b -> a < 0 -> b <= 0.
  Proof.
    intros. setoid_replace (a * b) with ((- a) * (- b)) in H by ring.
    apply lt0_iff_neg in H0. apply ge0_mul_reg_ge0 in H; auto.
    apply le0_iff_neg; auto.
  Qed.

  
  (** **** More properties  *)
  
  (* 0 <= a * a *)
  Lemma sqr_ge0 : forall a : A, a * a >= 0.
  Proof.
    intros.
    pose proof (lt_connected 0 a). destruct H as [H|[H|H]].
    - apply le_if_lt.
      pose proof (lt_mul_compat_r H H). rewrite ring_mul_0_l in H0; auto.
    - apply le_if_lt. rewrite lt_opp_iff in H. rewrite group_opp_0 in H.
      rewrite <- (group_opp_opp a). rewrite ring_mul_opp_opp.
      pose proof (lt_mul_compat_r H H). rewrite ring_mul_0_l in H0. auto.
    - rewrite <- H. rewrite (ring_mul_0_l 0). apply le_refl.
  Qed.
  
  (* 0 <= a -> 0 <= b -> a + b == 0 -> a == 0 *)
  Lemma add_eq0_imply_0_l : forall a b : A, 0 <= a -> 0 <= b -> a + b == 0 -> a == 0.
  Proof.
    intros. apply lt_le_cong in H, H0.
    destruct H as [H|H], H0 as [H0|H0]; try easy.
    - assert (a + b > 0 + 0). apply lt_add_compat; auto.
      rewrite H1 in H2. rewrite identityLeft in H2. apply lt_irrefl in H2. easy.
    - rewrite <- H0 in *. rewrite identityRight in H1. auto.
  Qed.

  (* 0 <= a -> 0 <= b -> a + b == 0 -> b == 0 *)
  Lemma add_eq0_imply_0_r : forall a b : A, 0 <= a -> 0 <= b -> a + b == 0 -> b == 0.
  Proof.
    intros. rewrite commutative in H1. apply add_eq0_imply_0_l in H1; auto.
  Qed.

  (** 0 <= a + b -> a >= - b *)
  Lemma sub_ge0_imply_ge : forall a b : A, 0 <= a - b -> a >= b.
  Proof.
    intros. apply le_add_compat_r with (c:= b) in H. ring_simplify in H. auto.
  Qed.

  (** 2 * a * b <= a² + b² *)
  Lemma mul_le_add_sqr : forall a b : A, 2 * a * b <= a² + b².
  Proof.
    intros.
    assert (0 <= (a - b)²). apply sqr_ge0.
    ring_simplify in H.
    setoid_replace (a ² + - (2 * a * b) + b ²)
      with (a ² + b ² - (2 * a * b)) in H by ring.
    apply sub_ge0_imply_ge in H. auto.
  Qed.


  (** *** Abs of a term of A type *)

  (* Tips: a good example shows that we can compare two object using 
     "cmp_dec" without "cmpb" (boolean version), thus avoids many proof works.
     That is, another choice are: also provide {Altb Aleb : A -> A -> bool},
     but we need more works *)
  Definition Aabs (a : A) : A := if le_dec 0 a then a else - a.
  Notation "| a |" := (Aabs a) : A_scope.

  (** 0 <= a -> | a | == a *)
  Lemma Aabs_right : forall a : A, 0 <= a -> | a | == a.
  Proof. intros. unfold Aabs. destruct (le_dec 0 a); try easy. Qed.
    
  (** a < 0 -> | a | == - a *)
  Lemma Aabs_left : forall a : A, a < 0 -> | a | == - a.
  Proof.
    intros. unfold Aabs. destruct (le_dec 0 a); try easy.
    apply lt_not_le in H. easy.
  Qed.

  (** | a * b | == | a | * | b | *)
  Lemma Aabs_mul : forall a b : A, | a * b | == | a | * | b |.
  Proof.
    intros. unfold Aabs.
    destruct (le_dec 0 (a*b)), (le_dec 0 a), (le_dec 0 b); try ring.
    - apply not_le_lt in n.
      rewrite commutative in a0. apply ge0_mul_reg_le0 in a0; auto.
      apply le_ge_eq in a1; auto. rewrite a1. ring.
    - apply not_le_lt in n. apply ge0_mul_reg_le0 in a0; auto.
      apply le_ge_eq in a1; auto. rewrite a1. ring.
    - pose proof (mul_ge0_if_ge0_ge0 a0 a1). easy.
    - apply not_le_lt in n,n0,n1. pose proof (mul_gt0_if_lt0_lt0 n0 n1).
      exfalso. apply (lt_gt_contr n H).
  Qed.

  (** | a + b | <= | a | + | b | *)
  Lemma Aabs_add_le : forall a b : A, | a + b | <= | a | + | b |.
  Proof.
    intros. unfold Aabs.
    destruct (le_dec 0 a), (le_dec 0 b), (le_dec 0 (a + b));
      ring_simplify.
    - apply le_refl.
    - apply le_add_compat; apply ge_neg_l_if_ge0; auto.
    - apply le_add_compat_l. apply le_neg_r_if_lt0; auto. apply not_le_lt; auto.
    - apply le_add_compat_r. apply ge_neg_l_if_ge0; auto.
    - apply le_add_compat_r. apply le_neg_r_if_lt0. apply not_le_lt; auto.
    - apply le_add_compat_l. apply ge_neg_l_if_ge0; auto.
    - apply not_le_lt in n,n0. pose proof (add_lt0_if_lt0_lt0 n n0).
      apply le_not_lt in a0. easy.
    - apply le_refl.
  Qed.

End theories.

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Field *)

(** ** Class *)
Class Field {A} Aadd (Azero:A) Aopp Amul Aone Ainv Aeq := {
    fieldRing :: ARing Aadd Azero Aopp Amul Aone Aeq;
    fieldAinvProper :: Proper (Aeq ==> Aeq) Ainv;
    field_mulInvL : forall a, ~(Aeq a Azero) -> Aeq (Amul (Ainv a) a) Aone;
    field_1_neq_0 : ~(Aeq Aone Azero);
    
    (* Tips: 也许还遗漏了一个条件，即：0 没有逆元。一个可能的方案如下：
       If we have "/0", then prove anything *)
    (* field_inv0_False : { x : A | x = Ainv Azero } -> False *)

    (* But, this is a bad idea. Because there exist "/0" in R.
       Rinv_0: / 0 = 0
       I can't deal with "/0" perfectly right now. *)
  }.
Coercion fieldRing : Field >-> ARing.

(** ** Theories *)

(** make a `field_theory` from `Field` *)
Lemma make_field_theory `(HField : Field)
  : field_theory Azero Aone Aadd Amul
      (fun x y => Aadd x (Aopp y)) Aopp
      (fun x y => Amul x (Ainv y)) Ainv Aeq.
  Proof.
    constructor; intros;
      try (rewrite ?identityLeft,?associative; reflexivity);
      try (rewrite commutative; reflexivity).
    apply (make_ring_theory fieldRing).
    apply field_1_neq_0.
    apply field_mulInvL. auto.
 Qed.

Section Theory.
  Context `{HField : Field}.
  Add Field field_inst : (make_field_theory HField).

  Infix "==" := Aeq.
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Notation Asub a b := (a + -b).
  Notation "0" := Azero.
  Notation "1" := Aone.
  Infix "*" := Amul.
  Notation "/ a" := (Ainv a).
  Notation Adiv a b := (a * (/b)).
  Infix "/" := Adiv.

  (** ~(a == 0) -> a * / a == 1 *)
  Lemma field_mulInvR : forall a : A, ~(a == 0) -> a * /a == 1.
  Proof. intros. rewrite commutative. rewrite field_mulInvL; easy. Qed.

  (** ~(a == 0) -> (1/a) * a == 1 *)
  Lemma field_mulInvL_inv1 : forall a : A, ~(a == 0) -> (1/a) * a == 1.
  Proof. intros. simpl. field; auto. Qed.
  
  (** ~(a == 0) -> a * (1/a) == 1 *)
  Lemma field_mulInvR_inv1 : forall a : A, ~(a == 0) -> a * (1/a) == 1.
  Proof. intros. simpl. field. auto. Qed.

  (** ~(a == 0) -> / ~(a == 0) *)
  Lemma field_inv_neq0_if_neq0 : forall a : A, ~(a == 0) -> ~(/ a == 0).
  Proof.
    intros. intro.
    pose proof (field_mulInvL H). rewrite H0 in H1. rewrite ring_mul_0_l in H1.
    apply field_1_neq_0. easy.
  Qed.

  (** ~(- 1 == 0) *)
  Lemma field_neg1_neq_0 : ~(- (1) == 0).
  Proof.
    intro. rewrite <- group_opp_0 in H at 1. apply group_opp_inj in H.
    apply field_1_neq_0; auto.
  Qed.
  
  (** ~(a == 0) -> a * b == a * c -> b == c *)
  Lemma field_mul_cancel_l : forall a b c : A,
      ~(a == 0) -> a * b == a * c -> b == c.
  Proof.
    intros.
    assert (/a * (a * b) == /a * (a * c)).
    { rewrite H0. easy. }
    rewrite <- ?associative in H1.
    rewrite field_mulInvL in H1; auto.
    rewrite ?identityLeft in H1. easy.
  Qed.

  (** ~(c == 0) -> a * c == b * c -> a == b *)
  Lemma field_mul_cancel_r : forall a b c : A,
      ~(c == 0) -> a * c == b * c -> a == b.
  Proof.
    intros.
    assert ((a * c) * /c == (b * c) * /c).
    { rewrite H0. easy. }
    rewrite ?associative in H1.
    rewrite field_mulInvR in H1; auto.
    rewrite ?identityRight in H1. easy.
  Qed.

  (** a * b == 1 -> / a == b *)
  Lemma field_inv_eq_l : forall a b : A, ~(a == 0) -> a * b == 1 -> / a == b.
  Proof.
    intros. apply (@field_mul_cancel_l a (/ a) b); auto.
    rewrite field_mulInvR; easy.
  Qed.

  (** a * b == 1 -> / b == a *)
  Lemma field_inv_eq_r : forall a b : A, ~(b == 0) -> a * b == 1 -> / b == a.
  Proof.
    intros. apply (@field_mul_cancel_r (/ b) a b); auto.
    rewrite field_mulInvL; auto. easy.
  Qed.

  (** / / a == a *)
  Lemma field_inv_inv : forall a : A, ~(a == 0) -> / / a == a.
  Proof.
    intros. pose proof (field_inv_neq0_if_neq0 H).
    apply field_mul_cancel_l with (/ a); auto.
    rewrite field_mulInvL; auto. rewrite field_mulInvR; auto. easy.
  Qed.

  (** / a == / b -> a == b *)
  Lemma field_inv_inj : forall a b : A, ~(a == 0) -> ~(b == 0) -> / a == / b -> a == b.
  Proof.
    intros. rewrite <- field_inv_inv; auto. rewrite H1.
    rewrite field_inv_inv; auto. easy.
  Qed.

  (** / (- a) == - (/ a) *)
  Lemma field_inv_opp : forall a : A, ~(a == 0) -> / (- a) == - (/ a).
  Proof.
    intros. apply field_inv_eq_l. apply group_opp_neq0_iff; auto.
    rewrite ring_mul_opp_opp. apply field_mulInvR; auto.
  Qed.

  
  Context {AeqDec : Dec Aeq}.
  
  (** a * b == 0 <-> a == 0 \/ b == 0 *)
  Lemma field_mul_eq0_iff : forall a b : A, a * b == 0 <-> a == 0 \/ b == 0.
  Proof.
    intros. split; intros.
    - destruct (dec _ a 0), (dec _ b 0); auto.
      exfalso.
      assert ((/a * a) * (b * /b) == /a * (a * b) * /b). field; auto.
      rewrite H, field_mulInvL, field_mulInvR, identityLeft in H0; auto.
      rewrite ring_mul_0_r in H0 at 1.
      rewrite ring_mul_0_l in H0 at 1.
      apply field_1_neq_0; auto.
    - destruct H; rewrite H. ring. ring.
  Qed.
  
  (** ~(a * b == 0) <-> (~(a == 0) /\ ~(b == 0)) *)
  Lemma field_mul_neq0_iff : forall a b : A,
      ~(a * b == 0) <-> (~(a == 0) /\ ~(b == 0)).
  Proof. intros. rewrite field_mul_eq0_iff. tauto. Qed.
    
  (** ~(/ a == 0) -> ~(a == 0) *)
  Lemma field_inv_neq0_imply_neq0 : forall a : A, ~(/ a == 0) -> ~(a == 0).
  Proof.
    intros. intro.
    (* 备注：
       1. 我暂时无法证明这个引理，但我可能要用到这个性质
       2. 由反证法，若 a == 0，则 /a == 0，这应该不对。因为：
          数学上，无穷小的倒数是无穷大。不过 0 还不是无穷小。
       3. 在 Reals.RIneq 库中，有两个引理如下，我觉得好像有问题，但又无法指正。
          Lemma Rinv_0 : / 0 == 0.
          Lemma Rinv_inv r : / / r == r.
       4. 主要问题是，/ 0 是没有定义的，但我的 Field 结构无法排除这种情况
     *)
  Admitted.

  (** / ~(a == 0) <-> ~(a == 0) *)
  Lemma field_inv_neq0_iff : forall a : A, ~(/ a == 0) <-> ~(a == 0).
  Proof.
    intros; split. apply field_inv_neq0_imply_neq0.
    apply field_inv_neq0_if_neq0.
  Qed.
  
  (** a * a == 0 -> a == 0 *)
  Lemma field_sqr_eq0_reg : forall a : A, a * a == 0 -> a == 0.
  Proof. intros. apply field_mul_eq0_iff in H. destruct H; auto. Qed.

  (** a * b == b -> a == 1 \/ b == 0 *)
  Lemma field_mul_eq_imply_a1_or_b0 : forall (a b : A),
      a * b == b -> (a == 1) \/ (b == 0).
  Proof.
    intros. destruct (dec _ a 1), (dec _ b 0); auto.
    setoid_replace b with (1 * b) in H at 2 by ring.
    apply field_mul_cancel_r in H; auto.
  Qed.

End Theory.

(** ** Instances *)
(* Section Instances. *)

(*   Import Qcanon Reals. *)
  
(*   #[export] Instance Field_Qc : Field Qcplus 0 Qcopp Qcmult 1 Qcinv eq. *)
(*   split_intro; subst; (try (field; reflexivity)); try easy. *)
(*   field. auto. *)
(*   Qed. *)

(*   #[export] Instance Field_R : Field Rplus R0 Ropp Rmult R1 Rinv eq. *)
(*   split_intro; subst; try (field; reflexivity); auto. *)
(*   field; auto. auto with real. *)
(*   Qed. *)

(* End Instances. *)

(** ** Examples *)
(* Section Examples. *)

(*   Import Reals. *)
(*   Open Scope R_scope. *)
  
(*   Goal forall a b : R, a <> 0 -> /a * a = 1. *)
(*   Proof. intros. apply field_mulInvL. auto. Qed. *)

(* End Examples. *)


(* ######################################################################### *)
(** * Field with total order *)

Class OrderedField {A} Aadd Azero Aopp Amul Aone Ainv Aeq Alt Ale := {
    ofField :: @Field A Aadd Azero Aopp Amul Aone Ainv Aeq;
    ofOrderedARing :: OrderedARing Aadd Azero Aopp Amul Aone Aeq Alt Ale;
  }.
Coercion ofField : OrderedField >-> Field.
Coercion ofOrderedARing : OrderedField >-> OrderedARing.

(** ** Theories *)
Section Theory.
  Context `{HOrderedField : OrderedField}.
  Add Field field_inst : (make_field_theory HOrderedField).

  Infix "==" := Aeq.
  Infix "+" := Aadd.
  Notation "- a" := (Aopp a).
  Notation "0" := Azero.
  Infix "*" := Amul.
  Notation "1" := Aone.
  Notation "/ a" := (Ainv a).
  Notation Adiv a b := (a * / b).
  Infix "/" := Adiv.
  
  Notation "a > b" := (Alt b a).
  Notation "a >= b" := (Ale b a).
  Infix "<" := Alt.
  Infix "<=" := Ale.
    
  (** ~(a == 0) -> 0 < a * a *)
  Lemma sqr_gt0 : forall a : A, ~(a == 0) -> 0 < a * a.
  Proof.
    intros. apply lt_if_le_and_neq.
    - apply sqr_ge0.
    - intro. symmetry in H0. apply field_sqr_eq0_reg in H0. easy.
  Qed.
  
  (** 0 < 1 *)
  Lemma lt_0_1 : 0 < 1.
  Proof.
    (* 0 < a*a -> 0 < 1*1 -> 0 < 1 *)
    pose proof (field_1_neq_0).
    pose proof (sqr_gt0 H). rewrite identityLeft in H0. auto.
  Qed.
  
  (** 0 <= 1 *)
  Lemma le_0_1 : 0 <= 1.
  Proof. apply le_if_lt. apply lt_0_1. Qed.
  
  (** 0 < a -> 0 < / a *)
  Lemma inv_gt0 : forall a : A, 0 < a -> 0 < / a.
  Proof.
    intros.
    assert (0 < a * / a).
    { field_simplify. apply lt_0_1. 
      intro. rewrite H0 in H. apply lt_irrefl in H; auto. }
    apply (gt0_mul_reg_gt0 H0); auto.
  Qed.
  
  (** a < 0 -> / a < 0 *)
  Lemma inv_lt0 : forall a : A, a < 0 -> / a < 0.
  Proof.
    intros. pose proof (lt_imply_neq H).
    rewrite lt_opp_iff in H. rewrite group_opp_0 in H.
    apply inv_gt0 in H. rewrite field_inv_opp in H; auto. apply lt0_iff_neg; auto.
  Qed.
  
  (** 0 < a -> 0 < b -> a < b -> / b < / a *)
  Lemma lt_inv : forall a b : A, 0 < a -> 0 < b -> a < b -> / b < / a.
  Proof.
    (* a < b -> /b * a * /a < /b * b * /a -> /b < /a *)
    intros.
    apply lt_mul_compat_l with (c:=/b) in H1.
    apply lt_mul_compat_r with (c:=/a) in H1.
    rewrite field_mulInvL in H1. rewrite identityLeft in H1 at 1.
    rewrite associative in H1. rewrite field_mulInvR, identityRight in H1. auto.
    symmetry_not. apply lt_imply_neq; auto.
    symmetry_not. apply lt_imply_neq; auto.
    apply inv_gt0; auto.
    apply inv_gt0; auto.
  Qed.

  (** 0 < c -> c * a < c * b -> a < b *)
  Lemma lt_mul_reg_l : forall a b c, 0 < c -> c * a < c * b -> a < b.
  Proof.
    intros. apply lt_mul_compat_l with (c:=/c) in H0.
    - rewrite <- !associative in H0. rewrite field_mulInvL in H0.
      + rewrite !identityLeft in H0; auto.
      + symmetry_not. apply lt_imply_neq; auto.
    - apply inv_gt0; auto.
  Qed.
  
  (** 0 < c -> a * c < b * c -> a < b *)
  Lemma lt_mul_reg_r : forall a b c, 0 < c -> a * c < b * c -> a < b.
  Proof.
    intros. rewrite !(commutative _ c) in H0. apply lt_mul_reg_l in H0; auto.
  Qed.
  
  (** 0 < a -> a < b -> a / b < 1 *)
  Lemma lt_imply_div_lt_1 : forall a b : A, 0 < a -> a < b -> a / b < 1.
  Proof.
    intros. setoid_replace 1 with (b / b).
    apply lt_mul_compat_r; auto. apply inv_gt0. apply lt_trans with a; auto.
    rewrite field_mulInvR; try easy.
    symmetry_not. apply lt_imply_neq. apply lt_trans with a; auto.
  Qed.
  
  (** 0 < a -> a <= b -> a / b <= 1 *)
  Lemma le_imply_div_le_1 : forall a b : A, 0 < a -> a <= b -> a / b <= 1.
  Proof.
    intros. apply lt_le_cong in H0. destruct H0.
    - apply le_if_lt. apply lt_imply_div_lt_1; auto.
    - rewrite <- H0. rewrite field_mulInvR. apply le_refl.
      symmetry_not. apply lt_imply_neq; auto.
  Qed.
    
End Theory.

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Convert to R type *)

(** "a2r: A -> R" is consistent with {+,0,-x,*,1,/x,==,<,<=}  *)
Class ConvertToR {A} Aadd Azero Aopp Amul Aone Ainv Aeq Alt Ale (a2r : A -> R)
  := {
    (* a2r (a + b) = a2r a + a2r b *)
    a2r_add : forall a b : A, a2r (Aadd a b) = (a2r a + a2r b)%R;
    (* a2r 0 = 0%R *)
    a2r_0 : a2r Azero = 0%R;
    (* a2r (- a) = - (a2r a) *)
    a2r_opp : forall a : A, a2r (Aopp a) = (- (a2r a))%R;
    (* a2r (a * b) = a2r a * a2r b *)
    a2r_mul : forall a b : A, a2r (Amul a b) = (a2r a * a2r b)%R;
    (* a2r 1 = 1 *)
    a2r_1 : a2r Aone = 1%R;
    (* ~(a == 0) -> a2r (/ a) = / (a2r a) *)
    a2r_inv : forall a : A, ~(Aeq a Azero) -> a2r (Ainv a) = (/ (a2r a))%R;
    (* Order {==, <, <=}  *)
    a2r_Order :: Order Aeq Alt Ale;
    (* a2r a = a2r b <-> a == b *)
    a2r_eq_iff : forall a b : A, a2r a = a2r b <-> Aeq a b;
    (* a2r a < a2r b <-> a < b *)
    a2r_lt_iff : forall a b : A, (a2r a < a2r b)%R <-> Alt a b;
    (* a2r a <= a2r b <-> a <= b *)
    a2r_le_iff : forall a b : A, (a2r a <= a2r b)%R <-> Ale a b
  }.

(** ** Theories *)
Section Theory.
  Context `{HConvertToR : ConvertToR}.
  Infix "==" := Aeq : A_scope.
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Infix "<" := Alt : A_scope.
  Infix "<=" := Ale : A_scope.

  (** a2r a = 0 <-> a == 0 *)
  Lemma a2r_eq0_iff : forall a : A, a2r a = 0%R <-> a == 0.
  Proof. intros. rewrite <- a2r_0. apply a2r_eq_iff. Qed.

  (** a2r a = 1 <-> a = 1 *)
  Lemma a2r_eq1_iff : forall a : A, a2r a = 1%R <-> a == 1.
  Proof. intros. rewrite <- a2r_1. apply a2r_eq_iff. Qed.
  
  (** 0 <= a2r a <-> 0 <= a *)
  Lemma a2r_ge0_iff : forall a : A, (0 <= a2r a)%R <-> 0 <= a.
  Proof. intros. rewrite <- a2r_0. apply a2r_le_iff. Qed.

  (** 0 < a2r a <-> 0 < a *)
  Lemma a2r_gt0_iff : forall a : A, (0 < a2r a)%R <-> (0 < a)%A.
  Proof. intros. rewrite <- a2r_0. apply a2r_lt_iff. Qed.

  Section OrderedARing.
    Context `{HOrderedARing :
        OrderedARing A Aadd 0 Aopp Amul 1 Aeq Alt Ale}.
    Notation "| a |" := (Rabs a) : R_scope.
    Notation "| a |" := (Aabs a) : A_scope.

    (** a2r | a | = | a2r a | *)
    Lemma a2r_Aabs : forall a : A, a2r (| a |) = | a2r a|%R.
    Proof.
      intros. unfold Aabs. destruct (le_dec 0 a).
      - rewrite Rabs_right; auto. rewrite <- a2r_0.
        apply Rle_ge. apply a2r_le_iff; auto.
      - rewrite Rabs_left. rewrite a2r_opp. auto.
        rewrite <- a2r_0. apply a2r_lt_iff. apply not_le_lt; auto.
    Qed.
    
  End OrderedARing.
  
End Theory.

(** ** Instances *)

(** ** Examples *)


(* ######################################################################### *)
(** * Metric space *)

(** Adist:A×A→R(>=0) is a metric over A, if it satisfy three axioms.
    Then, (A, Adist) is called a metric space, and Adist(a,b) is called the 
    distance between point a and b in (A,dist)     *)
Class MetricSpace {A} (Adist : A -> A -> R) Aeq := {
    ms_gt0 : forall a b : A, (R0 <= Adist a b)%R;
    ms_eq0_iff_eq : forall a b : A, Adist a b = R0 <-> Aeq a b;
    ms_sym : forall a b : A, Adist a b = Adist b a;
    ms_tri_ineg : forall a b c : A, (Adist a c <= Adist a b + Adist b c)%R
  }.

(** ** Theories *)

(** ** Instances *)

(** ** Examples *)
