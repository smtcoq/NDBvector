(**************************************************************************)
(*                                                                        *)
(*     NDBvector                                                          *)
(*     Copyright (C) 2015                                                 *)
(*                                                                        *)
(*     Tianyi Liang                                                       *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     The University of Iowa                                             *)
(*     LRI - Université Paris Sud - Université Paris Saclay               *)
(*                                                                        *)
(*   TODO: This file is distributed under the terms of SOME licence       *)
(*                                                                        *)
(**************************************************************************)


Require Import List NArith.
Import N.

Local Open Scope list_scope.
Local Open Scope N_scope.

Set Implicit Arguments.
Unset Strict Implicit.


(** Some useful functions *)

Section Map2.

  Variables A B C : Type.
  Variable f : A -> B -> C.

  Fixpoint map2 (l1 : list A) (l2 : list B) : list C :=
    match l1, l2 with
    | b1::tl1, b2::tl2 => (f b1 b2)::(map2 tl1 tl2)
    | _, _ => nil
    end.

End Map2.


(** * Representation of bit vectors and implementation of standard
      operations *)

Module BV.

  (** The type of bit vectors *)
  Definition t := (list bool * N)%type.

  (** The empty bit vector *)
  Definition empty : t := (nil, 0).

  (** Test weither a bit vector is empty *)
  Definition is_empty (bv : t) : bool :=
    let (_, n) := bv in
    match n with
    | N0 => true
    | _ => false
    end.

  (** Test weither a bit vector is zero (this defines the semantics of
      the 0 bit vector) *)
  Definition is_zero (bv : t) : bool :=
    let (b, _) := bv in
    List.forallb (fun x => negb x) b.

  (** Concatenation of two bit vectors *)
  Definition concat (bv1 bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (b1 ++ b2, n1 + n2).

  (** Bitwise not *)
  Definition not (bv : t) : t :=
    let (b, n) := bv in
    (List.map negb b, n).

  (** Bitwise and *)
  Definition and (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (map2 andb b1 b2, n1).

  (** Bitwise or *)
  Definition or (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (map2 orb b1 b2, n1).

  (** Bitwise xor *)
  Definition xor (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (map2 xorb b1 b2, n1).

  (** Lower weight bit *)
  Definition lower (bv : t) : bool :=
    let (b, _) := bv in
    List.hd false b.

  (** Higher weight bit *)
  Definition high (bv : t) : bool :=
    let (b, _) := bv in
    List.last b false.

  (** Left shift *)
  Definition shiftleft (bv : t) : t :=
    let (b, n) := bv in
    (false::(List.removelast b), n).

  (** Right shift *)
  Definition shiftright (bv : t) : t :=
    let (b, n) := bv in
    ((List.tl b) ++ (false::nil), n).

  (** Left shift of [n] bits *)
  Fixpoint shiftleft_n (bv : t) (n : nat) : t :=
    match n with
      | O => bv
      | S n2 => shiftleft_n (shiftleft bv) n2
    end.

  (** Right shift of [n] bits *)
  Fixpoint shiftright_n (bv : t) (n : nat) : t :=
    match n with
      | O => bv
      | S n2 => shiftright_n (shiftright bv) n2
    end.

  (** Computes the [i]th bit *)
  Definition bb_nth (i : nat) (bv : t) : bool :=
    let (b, _) := bv in
    nth i b false.

  (** Computation of the unsigned integer represented by a bit vector *)
  Fixpoint b2p (b : list bool) : option positive :=
    match b with
    | nil => None
    | false::b =>
      match b2p b with
      | Some p => Some (xO p)
      | None => None
      end
    | true::b =>
      match b2p b with
      | Some p => Some (xI p)
      | None => Some xH
      end
    end.

  Definition bv2n (bv : t) : N :=
    let (b, _) := bv in
    match b2p b with
    | None => N0
    | Some p => Npos p
    end.

  (** Computation of the bit vector representing an integer *)
  Fixpoint p2bv (p : positive) : t :=
    match p with
    | xO p =>
      let (b,n) := p2bv p in
      (false::b, n+1)
    | xI p =>
      let (b,n) := p2bv p in
      (true::b, n+1)
    | xH => (true::nil, 1)
    end.

  Definition n2bv (n : N) : t :=
    match n with
    | N0 => (false::nil, 1)
    | Npos p => p2bv p
    end.

  Definition n2b (n : N) : list bool :=
    let (b, _) := n2bv n in b.

  (* We may want to change the definition of arithmetic operations *)
  (** Addition *)
  Definition add (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 + n4) in
    let b3 := (n2b n5) in
    (b3, n1).

  (** Subtraction *)
  Definition sub (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 - n4) in
    let b3 := (n2b n5) in
    (b3, n1).

  (** Multiplication *)
  Definition mul (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 * n4) in
    let b3 := (n2b n5) in
    (b3, n1).

  (** Negation *)
  Definition neg (bv1 : t) (n : N) : t :=
    let (b1, n1) := bv1 in
    let n2 := 2 ^ n in
    let n3 := (bv2n bv1) in
    let n4 := n2 - n3 in
    ((n2b n4), n).

  (** Division *)
  Definition udiv (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n4 := (bv2n bv2) in
    match n4 with
      | 0 => (nil, 0)
      | _ =>
      let n3 := (bv2n bv1) in
      ((n2b (n3 / n4)), n1)
    end.

  (** Reminder *)
  Definition urem (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n4 := (bv2n bv2) in
    match n4 with
      | 0 => (nil, 0)
      | _ =>
      let n3 := (bv2n bv1) in
      ((n2b (n3 mod n4)), n1)
    end.

  (** Unsigned less than *)
  Definition ult (bv1 : t) (bv2 : t) :=
    let n1 := (bv2n bv1) in
    let n2 := (bv2n bv2) in
    (n1 < n2).

  (** Drops the [n] bits of lowest weight *)
  Fixpoint drop_n (l : list bool) (n : nat) : list bool :=
    match n with
      | O => l
      | S n2 => drop_n (@List.tl bool l) n2
    end.

  (** Keep the [n] bits of lowest weight *)
  Fixpoint first_n (l : list bool) (n : nat) : list bool :=
    match n with
      | O => nil
      | S n2 =>
      match l with
        | nil => nil
        | x :: l2 => x :: (first_n l2 n2)
      end
    end.

  (** Extracts the bits between i (included) and j (excluded) *)
  Definition extract (l : list bool) (i : nat) (j : nat) : list bool :=
    let l2 := drop_n l i in
    (first_n l2 j).

End BV.



(* Module BVProof. *)

(*   Import BV. *)

(*   Definition bitof (bv : t)(m : nat) := *)
(*     bb_nth m bv. *)

(*   Definition bblt_len (bv : t) := *)
(*     let (b, n) := bv in *)
(*     n. *)




(*   Definition wf (bv:t) : Prop := *)
(*      let (b,n) := bv in N.of_nat (length b) = n. *)

(*   Check N.of_nat. *)
(*   Print N.of_nat. *)
(*   SearchAbout N.of_nat. *)
(*   Search (N.of_nat (_ + _) = (N.of_nat _) + (N.of_nat _)). *)

(*   Lemma concat_wf : forall (bv1 bv2:t), wf bv1 -> wf bv2 -> wf (concat bv1 bv2). *)
(*   Proof. *)
(*     intros [b1 n1] [b2 n2] H1 H2. *)
(*     simpl. *)
(*     Search ((length (_ ++ _)) = ((length _) + (length _))%nat). *)
(*     SearchAbout length. *)
(*     rewrite app_length. *)
(*     rewrite Nat2N.inj_add. *)
(*     simpl in H1. simpl in H2. *)
(*     rewrite H1. rewrite H2. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Lemma nth_append1 : forall A (l1 l2:list A) (i:nat) (d:A), *)
(*     (i < length l1)%nat -> nth i (l1 ++ l2) d = nth i l1 d. *)
(*   Proof. *)
(*     intros A. induction l1. *)
(*     - simpl. Search (~ ((_ < 0)%nat)). *)
(*       intros l2 i d H. elim (Lt.lt_n_0 _ H). *)
(*     - simpl. intros l2 [ |i] d Hi. *)
(*       * reflexivity. *)
(*       * apply IHl1. apply Lt.lt_S_n. assumption. *)
(*   Qed. *)

(*   Lemma of_nat_lt : forall i j, *)
(*     (of_nat i < of_nat j) -> (i < j)%nat. *)
(*   Admitted. *)

(*   Check nth. *)
(*   Lemma nth_wf : forall(bv1 bv2:t) (i : nat), *)
(*    let (b1, n1) := bv1 in *)
(*    wf bv1 -> wf bv2 -> (of_nat i < n1) -> bb_nth i (concat bv1 bv2) = bb_nth i bv1. *)
(*   Proof. *)
(*    intros [b1 n1] [b2 n2]. simpl. intros i H1 H2 Hi. *)
(*    rewrite nth_append1. *)
(*      - reflexivity. *)
(*      - rewrite <- H1 in Hi. *)
(*        apply of_nat_lt. *)
(*        assumption. *)
(*   Qed. *)
