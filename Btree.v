Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Bool.

Inductive TreeNat : Type :=
| NilNat  : TreeNat
| LeafNat : list nat -> TreeNat
| NodeNat : list nat -> list TreeNat -> TreeNat.

Arguments NilNat.
Arguments LeafNat _.
Arguments NodeNat _ _.

Definition btree_example : TreeNat :=
  NodeNat [100] [

    NodeNat [35; 65] [
      LeafNat [10];
      LeafNat [40; 50];
      LeafNat [70; 80; 90]
    ];

    NodeNat [130; 180] [
      LeafNat [110; 120];
      LeafNat [140; 160];
      LeafNat [190; 240; 260]
    ]
  ].
  



(* 1. Every node has at most [m] children *)
Fixpoint check_max_children_nat (m : nat) (t : TreeNat) : bool :=
  match t with
  | NilNat => true
  | LeafNat _ => true
  | NodeNat _ children =>
      leb (length children) m
      && forallb (check_max_children_nat m) children
  end.

  Definition bad_btree_example_most_m_children : TreeNat :=
  NodeNat [100] [
    LeafNat [10];
    LeafNat [20];
    LeafNat [30];
    LeafNat [40]  (* This is the 4th child, which violates m=3 *)
  ].

Eval compute in check_max_children_nat 3 btree_example. (*true*)
Eval compute in check_max_children_nat 3 bad_btree_example_most_m_children. (*false*)

(* 2. Every non-root internal node has at least [m/2] children *)
Fixpoint check_min_children'_nat (is_root : bool) (m : nat) (t : TreeNat) : bool :=
  match t with
  | NilNat => true
  | LeafNat _ => true
  | NodeNat _ children =>
      let min_req := Nat.div2 m in
      (if is_root then true else leb min_req (length children))
      && forallb (fun c => check_min_children'_nat false m c) children
  end.

Definition check_min_children_nat (m : nat) (t : TreeNat) : bool :=
  check_min_children'_nat true m t.

Definition bad_min_children_example : TreeNat :=
  NodeNat [100] [

    NodeNat [50] [  (* non-root node - only 1 child < 2 *)
      LeafNat [10]
    ];

    NodeNat [150] [
      LeafNat [110];
      LeafNat [160]
    ]
  ].

Eval compute in check_min_children_nat 4 btree_example. (* true *)

Eval compute in check_min_children_nat 4 bad_min_children_example. (* false *)


(* 3. The root has at least two children (unless it is a leaf). *)
Definition check_root_children_nat (t : TreeNat) : bool :=
  match t with
  | NodeNat _ children => leb 2 (length children)
  | _ => true
  end.

  Definition bad_root_children_example : TreeNat :=
  NodeNat [100] [  (* Root node with only 1 child *)
    LeafNat [50]
  ].

Eval compute in check_root_children_nat btree_example. (* true *)

Eval compute in check_root_children_nat bad_root_children_example. (* false *)


(* 4. All leaves are on the same level. *)
Fixpoint collect_leaf_levels_nat (t : TreeNat) (d : nat) : list nat :=
  match t with
  | NilNat => []
  | LeafNat _ => [d]
  | NodeNat _ children =>
      flat_map (fun c => collect_leaf_levels_nat c (S d)) children
  end.

Definition all_equal_nat (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => forallb (Nat.eqb x) xs
  end.

Definition check_all_leaves_same_level_nat (t : TreeNat) : bool :=
  all_equal_nat (collect_leaf_levels_nat t 0).

Definition bad_leaf_levels_example : TreeNat :=
  NodeNat [100] [

    LeafNat [50];  (* depth 1 *)

    NodeNat [150] [  (* depth 1, child goes to depth 2 *)
      LeafNat  [160]
    ]
  ].

Eval compute in check_all_leaves_same_level_nat btree_example. (* true *)

Eval compute in check_all_leaves_same_level_nat bad_leaf_levels_example. (* false *)


(* 5. A non-leaf node with [k] children contains [k−1] keys. *)
Fixpoint valid_btree_children_key_relation_nat (t : TreeNat) : bool :=
  match t with
  | NilNat => true
  | LeafNat _ => true
  | NodeNat keys children =>
      Nat.eqb (length children) (length keys + 1)
      && forallb valid_btree_children_key_relation_nat children
  end.

Definition bad_key_child_relation_example : TreeNat :=
  NodeNat [100; 150] [  (* 2 keys, but only 2 children instead of 3 *)
    LeafNat [50];
    LeafNat [160]
  ].

Eval compute in valid_btree_children_key_relation_nat btree_example. (* true *)

Eval compute in valid_btree_children_key_relation_nat bad_key_child_relation_example. (* false *)


(* 6. Ordered. *)
Fixpoint interleave_nat (ll : list (list nat)) (ks : list nat) : list nat :=
  match ll, ks with
  | [],      []       => []
  | l :: ls, k :: ks' => l ++ k :: interleave_nat ls ks'
  | [l],     []       => l
  | _,       _        => []
  end.

Fixpoint flatten_btree_nat (t : TreeNat) : list nat :=
  match t with
  | NilNat => []
  | LeafNat keys => keys
  | NodeNat keys children =>
      interleave_nat (map flatten_btree_nat children) keys
  end.

Fixpoint sorted_nat (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: ys => Nat.leb x y && sorted_nat xs
    end
  end.

Definition check_btree_sorted_nat (t : TreeNat) : bool :=
  sorted_nat (flatten_btree_nat t).
  
Definition bad_btree_example : TreeNat :=
  NodeNat [100] [

    NodeNat [35; 65] [
      LeafNat [10];
      LeafNat [40; 50];
      LeafNat [70; 20]   (* 20 < 70, violates sorted order *)
    ];

    NodeNat [130; 180] [
      LeafNat [110; 120];
      LeafNat [140; 160];
      LeafNat [190; 240; 260]
    ]
  ].
  
Eval compute in check_btree_sorted_nat btree_example. (* true *)

Eval compute in check_btree_sorted_nat bad_btree_example. (* false *)


(* 7. The tree is balanced. *)
Fixpoint collect_leaf_depths_nat (t : TreeNat) (d : nat) : list nat :=
  match t with
  | NilNat => [d]
  | LeafNat _ => [d]
  | NodeNat _ children =>
      flat_map (fun c => collect_leaf_depths_nat c (S d)) children
  end.

Definition is_btree_balanced_nat (t : TreeNat) : bool :=
  all_equal_nat (collect_leaf_depths_nat t 0).

Definition bad_balanced_example : TreeNat :=
  NodeNat [100] [
    LeafNat [50];  (* depth 1 *)

    NodeNat [150] [  (* depth 1 -> leads to depth 2 *)
      LeafNat [160]
    ]
  ].

Eval compute in is_btree_balanced_nat btree_example. (* true *)

Eval compute in is_btree_balanced_nat bad_balanced_example. (* false *)


(* Combined bree *)
Definition is_btree_nat (m : nat) (t : TreeNat) : bool :=
  check_max_children_nat m t
  && check_min_children_nat m t
  && check_root_children_nat t
  && check_all_leaves_same_level_nat t
  && valid_btree_children_key_relation_nat t
  && check_btree_sorted_nat t
  && is_btree_balanced_nat t.

(* Search *)
(* search a sorted list of keys *)
Fixpoint search_keys_nat (keys : list nat) (x : nat) : bool :=
  match keys with
  | [] => false
  | k :: ks =>
    match Nat.compare x k with
    | Eq => true
    | Lt => false
    | Gt => search_keys_nat ks x
    end
  end.

(* search the whole tree *)
Fixpoint search_nat (t : TreeNat) (x : nat) : bool :=
  match t with
  | NilNat => false
  | LeafNat keys => search_keys_nat keys x
  | NodeNat keys children =>
      let fix aux (cs : list TreeNat) (ks : list nat) {struct cs} : bool :=
        match cs with
        | [] => false
        | c :: cs' =>
          match ks with
          | [] => search_nat c x
          | k :: ks' =>
            match Nat.compare x k with
            | Eq => true
            | Lt => search_nat c x
            | Gt => aux cs' ks'
            end
          end
        end
      in aux children keys
  end.

Eval compute in search_nat btree_example 10.   (* = true  *)
Eval compute in search_nat btree_example 50.   (* = true  *)
Eval compute in search_nat btree_example 65.   (* = true  *)
Eval compute in search_nat btree_example 7.    (* = false *)
Eval compute in search_nat btree_example 175.  (* = false *)

(* Insertion *)

(* maximum number of keys for order [m] *)
Definition max_keys_nat (m : nat) : nat := 2*m - 1.

Fixpoint tree_size_nat (t : TreeNat) : nat :=
  match t with
  | NilNat => 1
  | LeafNat ks => 1 + length ks
  | NodeNat ks cs =>
      1 + length ks + fold_left (fun acc c => acc + tree_size_nat c) cs 0
  end.

(* test if a node is full *)
Definition full_nat (m : nat) (t : TreeNat) : bool :=
  match t with
  | NilNat => false
  | LeafNat ks => length ks =? max_keys_nat m
  | NodeNat ks _ => length ks =? max_keys_nat m
  end.

(* insert into a sorted list *)
Fixpoint insert_sorted_nat (ks : list nat) (x : nat) : list nat :=
  match ks with
  | [] => [x]
  | y :: ys =>
    match Nat.compare x y with
    | Lt | Eq => x :: ks
    | Gt => y :: insert_sorted_nat ys x
    end
  end.

Fixpoint replace_nth_nat {B} (n : nat) (b : B) (ls : list B) : list B :=
  match n, ls with
  | _, [] => []
  | 0, _ :: xs => b :: xs
  | S n', y :: ys => y :: replace_nth_nat n' b ys
  end.

Fixpoint find_index_nat {A'} (p : A' -> bool) (l : list A') (n : nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => if p x then Some n else find_index_nat p xs (S n)
  end.

Definition find_index_start_nat {A'} (p : A' -> bool) (l : list A') : option nat :=
  find_index_nat p l 0.

(* split a full node *)
Definition split_nat (m : nat) (t : TreeNat) : TreeNat :=
  match t with
  | LeafNat ks =>
      let i := length ks / 2 in
      let L := firstn i ks in
      let R := skipn i ks in
      match R with
      | mid :: R' => NodeNat [mid] [LeafNat L; LeafNat R']
      | [] => LeafNat ks
      end
  | NodeNat ks cs =>
      let i  := length ks / 2 in
      let Lk := firstn i ks in
      let Rk := skipn i ks in
      let Lc := firstn (i+1) cs in
      let Rc := skipn (i+1) cs in
      match Rk, Lc, Rc with
      | mid :: Rk', Lc', Rc' =>
          NodeNat [mid]
            [ NodeNat Lk  Lc'
            ; NodeNat Rk' Rc' ]
      | _, _, _ => NodeNat ks cs
      end
  | NilNat => t
  end.

Fixpoint insert_non_full_aux_nat (fuel : nat) (m : nat) (t : TreeNat) (x : nat) : TreeNat :=
  match fuel with
  | 0 => t
  | S fuel' =>
    match t with
    | NilNat => LeafNat [x]
    | LeafNat ks =>
        let ks' := insert_sorted_nat ks x in
        if length ks' <=? max_keys_nat m
        then LeafNat ks'
        else split_nat m (LeafNat ks')
    | NodeNat ks cs =>
        let idx :=
          find_index_start_nat
            (fun k => match Nat.compare x k with Lt | Eq => true | Gt => false end)
            ks
        in
        let i := match idx with Some n => n | None => length ks end in
        let c0 := nth i cs (LeafNat []) in
        let c1 := if full_nat m c0 then split_nat m c0 else c0 in
        let c2 := insert_non_full_aux_nat fuel' m c1 x in
        let rebuilt := NodeNat ks (replace_nth_nat i c2 cs) in
        if full_nat m rebuilt then split_nat m rebuilt else rebuilt
    end
  end.

Definition insert_non_full_nat (m : nat) (t : TreeNat) (x : nat) : TreeNat :=
  insert_non_full_aux_nat (tree_size_nat t) m t x.

(* insert *)
Definition insert_nat (m : nat) (t : TreeNat) (x : nat) : TreeNat :=
  if full_nat m t
  then insert_non_full_nat m (split_nat m t) x
  else insert_non_full_nat m t x.

(* Verify by flattening *)
Definition flatten_after_insert_nat (m : nat) (t : TreeNat) (x : nat) : list nat :=
  flatten_btree_nat (insert_nat m t x).

Fixpoint list_eqb_nat (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x::xs, y::ys => Nat.eqb x y && list_eqb_nat xs ys
  | _, _ => false
  end.

Definition verify_insert_flatten_nat (m : nat) (t : TreeNat) (x : nat) : bool :=
  let flat1 := flatten_after_insert_nat m t x in
  let flat2 := insert_sorted_nat (flatten_btree_nat t) x in
  list_eqb_nat flat1 flat2.
  
(* Inserting value 25 into btree_example *)
Eval compute in (
  let t' := insert_nat 3 btree_example 25 in
  is_btree_nat 3 t'
).
(* Expected: true *)

Eval compute in (
  flatten_after_insert_nat 3 btree_example 25
).
(* Expected: flatten_btree_nat btree_example with 25 inserted in order *)

Eval compute in (
  verify_insert_flatten_nat 3 btree_example 25
).
(* Expected: true *)

(* Inserting value 5 into btree_example *)
Eval compute in (
  let t' := insert_nat 3 btree_example 5 in
  is_btree_nat 3 t'
).
(* Expected: true *)

Eval compute in (
  flatten_after_insert_nat 3 btree_example 5
).
(* Expected: flatten_btree_nat btree_example with 5 inserted in order *)

Eval compute in (
  verify_insert_flatten_nat 3 btree_example 5
).
(* Expected: true *)

(* Inserting duplicate value (already present) *)
Eval compute in (
  verify_insert_flatten_nat 3 btree_example 65
).
(* Expected: true – 65 is inserted again but list stays sorted *)

(* Inserting very large value *)
Eval compute in (
  verify_insert_flatten_nat 3 btree_example 999
).
(* Expected: true *)

(*------------------------------------------------------------*)
Require Import Coq.Arith.PeanoNat.

(* if xs was sorted, inserting x yields another sorted list. *)
Require Import Lia.

Lemma insert_sorted_nat_sorted :
  forall x xs,
    sorted_nat xs = true ->
    sorted_nat (insert_sorted_nat xs x) = true.
Proof.
  intros x xs Hs.
  induction xs as [| y ys IH]; simpl in *.
  - reflexivity.
  - destruct (Nat.compare x y) eqn:Cmp; simpl.
    + (* x = y *)
      apply andb_true_intro; split.
      * apply Nat.leb_le. apply Nat.compare_eq_iff in Cmp. subst. lia.
      * simpl in Hs. assumption.
    + (* x < y *)
      apply andb_true_intro; split.
      * apply Nat.leb_le. apply Nat.compare_lt_iff in Cmp. lia.
      * simpl in Hs. assumption.
    + (* x > y *)
      destruct ys as [| z zs].
      * (* ys = [] *)
        simpl in Hs. apply andb_true_intro; split.
        -- apply Nat.leb_le. apply Nat.compare_gt_iff in Cmp. lia.
        -- simpl. reflexivity.
      * (* ys = z :: zs *)
        simpl in Hs. apply andb_true_iff in Hs as [Hyz Hsorted]. 
        (* apply andb_true_intro; split. *)
        admit.
        
Admitted.
 (*------------------------------------------*)
Lemma list_eqb_nat_eq :
  forall l1 l2,
    list_eqb_nat l1 l2 = true ->
    l1 = l2.
Proof.
  induction l1 as [| x xs IH]; destruct l2 as [| y ys]; simpl; intros H.
  - reflexivity.
  - discriminate.
  - discriminate.
  - apply andb_prop in H as [Hx Hrest].
    apply Nat.eqb_eq in Hx.
    apply IH in Hrest.
    subst. reflexivity.
Qed.

Lemma insert_preserves_sortedness :
  forall m t x,
    check_btree_sorted_nat t = true ->
    check_btree_sorted_nat (insert_nat m t x) = true.
Proof.
  intros m t x Hsorted.
  unfold check_btree_sorted_nat in *.

  remember (verify_insert_flatten_nat m t x) as b eqn:Heq.
  unfold verify_insert_flatten_nat in Heq.
  (* apply list_eqb_nat_eq in Heq. *)
  admit.
  (* rewrite Heq.
  apply insert_sorted_nat_sorted.
  assumption. *)
Admitted.


(*-----------------------------------------------------*)

(*If the original tree t is a valid B-tree, 
then after inserting x, the resulting tree still has a valid root:

    - If it's a leaf, it's ok.

    - If it's a Node, it has at least 2 children.*)
Section proofs.
Variable m : nat.
Hypothesis m_big_enough : max_keys_nat m > 0.


Lemma split_nat_node_has_two_children :
  forall t,
    full_nat m t = true ->
    match split_nat m t with
    | NodeNat _ children => length children = 2
    | _ => True
    end.
Proof.
  intros t Hfull.
  destruct t as [ | ks | ks cs].
  - (* Case: NilNat *)
    simpl in Hfull. discriminate.
  - (* Case: LeafNat *)
    simpl in Hfull.
    unfold split_nat.
    remember (length ks / 2) as i eqn:Heqi.
    destruct (skipn i ks) as [| mid R'] eqn:Hskip.
    + (* returns Leaf *)
      simpl. trivial.
    + (* returns Node with 2 Leaf children *)
      simpl. reflexivity.
  - (* Case: NodeNat *)
    simpl in Hfull.
    unfold split_nat.
    remember (length ks / 2) as i eqn:Heqi.
    destruct (skipn i ks) as [| mid Rk'] eqn:HRk.
    + (* returns original node *)
      simpl. exfalso.
      (* this follows from m_big_enough, and skipn (length ks /2) ks = [] ==> ks => [] *)
      admit.
    + simpl. reflexivity.
Admitted.

Lemma split_nat_not_full t :
full_nat m (split_nat m t) = false.
Proof. Admitted.

Lemma split_nat_btree t : is_btree_nat m t = true -> is_btree_nat m (split_nat m t) = true.
Proof. Admitted.

Lemma insert_aux_preserves_root_children' :
forall fuel x t ks cs, full_nat m t = false -> is_btree_nat m t = true ->
insert_non_full_aux_nat fuel m t x = NodeNat ks cs -> length cs >= 2. 
Proof.
  intros fuel. destruct fuel as [|fuel].
  -  simpl. intros. (* follows from H1 , H0 *) admit.
  - intros x y t ks cs Hfull Hbtree.
    simpl. 
Admitted.

Lemma insert_aux_preserves_root_children :
forall fuel x t, full_nat m t = false -> is_btree_nat m t = true ->
check_root_children_nat (insert_non_full_aux_nat fuel m t x) = true. 
Proof. (* follow from  insert_aux_preserves_root_children' *) Admitted.

Lemma insert_preserves_root_children :
  forall (x : nat) (t : TreeNat),
    is_btree_nat m t = true ->
    check_root_children_nat (insert_nat m t x) = true.
Proof.
  intros x t Hvalid.

  unfold insert_nat.
  remember (full_nat m t) as is_full eqn:Hfull.

  destruct is_full.
  - (* Root is full: insert after splitting the root *)
    (* After splitting, the result is always a Node with two children *)
    (* First, split the root *)
    remember (split_nat m t) as t2.
    unfold insert_non_full_nat.
    apply insert_aux_preserves_root_children.
    + subst t2. apply split_nat_not_full.
    + subst t2. apply split_nat_btree. assumption.
  - apply insert_aux_preserves_root_children; auto.
Qed.

(* helps me show that length (children of split_nat m t) = 2 *)






