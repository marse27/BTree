Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Bool.



Inductive Tree (A : Type) : Type :=
| Nil : nat -> Tree A
| Leaf : nat -> list A -> Tree A
| Node : nat -> list A -> list (Tree A) -> Tree A.

(*-----------------------------------------------------------------------------------------*)

Definition btree_example : Tree nat :=
  Node nat 100 [100] [

    Node nat 65 [35; 65] [
      Leaf nat 10 [10];
      Leaf nat 20 [40; 50];
      Leaf nat 30 [70; 80; 90]
    ];

    Node nat 180 [130; 180] [
      Leaf nat 40 [110; 120];
      Leaf nat 50 [140; 160];
      Leaf nat 60 [190; 240; 260]
    ]
  ].

Definition bad_btree_example : Tree nat :=
  Node nat 100 [100] [

    Node nat 65 [35; 65] [
      Leaf nat 10 [10];
      Leaf nat 20 [40; 50];
      Leaf nat 30 [70; 20]   (* 20 < 70 *)
    ];

    Node nat 180 [130; 180] [
      Leaf nat 40 [110; 120];
      Leaf nat 50 [140; 160];
      Leaf nat 60 [190; 240; 260]
    ]
  ].

(*-----------------------------------------------------------------------------------------*)

Arguments Nil  {A} _.
Arguments Leaf {A} _ _.
Arguments Node {A} _ _ _.

(*-----------------------------------------------------------------------------------------*)

(* Every node has at most m children. *)

Fixpoint check_max_children {A : Type} (m : nat) (t : Tree A) : bool :=
  match t with
  | Nil _ => true
  | Leaf _ _ => true
  | Node _ _ children =>
      let len := length children in
      let check_children := forallb (check_max_children m) children in
      leb len m && check_children
  end.

Eval compute in check_max_children 3 btree_example.

(*-----------------------------------------------------------------------------------------*)

(* Every node, except for the root and the leaves, has at least [m/2] children. *)

Fixpoint check_min_children' {A : Type} (is_root : bool) (m : nat) (t : Tree A) : bool :=
  match t with
  | Nil _ => true
  | Leaf _ _ => true
  | Node _ _ children =>
      let min_required := Nat.div2 m in
      let len := length children in
      let this_ok := if is_root then true else leb min_required len in
      let check_children := forallb (check_min_children' false m) children in
      this_ok && check_children
  end.

Definition check_min_children {A : Type} (m : nat) (t : Tree A) : bool :=
  check_min_children' true m t.

Eval compute in check_min_children 3 btree_example.

(*-----------------------------------------------------------------------------------------*)

(* The root node has at least two children unless it is a leaf. *)

Definition check_root_children {A : Type} (t : Tree A) : bool :=
  match t with
  | Nil _ => true
  | Leaf _ _ => true
  | Node _ _ children =>
      leb 2 (length children)
  end.

Eval compute in check_root_children btree_example.

(*-----------------------------------------------------------------------------------------*)

(* All leaves appear on the same level. *)
Fixpoint collect_leaf_levels {A : Type} (t : Tree A) (depth : nat) : list nat :=
  match t with
  | Nil _=> []
  | Leaf _ _ => [depth]
  | Node _ _ children =>
      flat_map (fun c => collect_leaf_levels c (S depth)) children
  end.

Definition all_equal (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => forallb (fun y => Nat.eqb y x) xs
  end.

Definition check_all_leaves_same_level {A : Type} (t : Tree A) : bool :=
  all_equal (collect_leaf_levels t 0).

Eval compute in check_all_leaves_same_level btree_example.

(*-----------------------------------------------------------------------------------------*)

(* A non-leaf node with k children contains k-1 keys. *)

Fixpoint valid_btree_children_key_relation {A : Type} (t : Tree A) : bool :=
  match t with
  | Nil _=> true
  | Leaf _ _ => true
  | Node _ keys children =>
      let key_count := length keys in
      let child_count := length children in
      Nat.eqb child_count (key_count + 1)
      && forallb valid_btree_children_key_relation children
  end.

Compute valid_btree_children_key_relation btree_example.

(*-----------------------------------------------------------------------------------------*)

(* The btree is sorted *)


Fixpoint interleave {A : Type} (ll : list (list A)) (ks : list A) {struct ll} : list A :=
  match ll, ks with
  | [],      []       => []
  | l :: ls, k :: ks' => l ++ k :: interleave ls ks'
  | [l],     []       => l
  | _,       _        => []    (* lengths don’t match → default [] *)
  end.


Fixpoint flatten_btree {A : Type} (t : Tree A) : list A :=
  match t with
  | Nil _        => []
  | Leaf _ keys  => keys
  | Node _ keys children =>
      let child_lists := map flatten_btree children in
      interleave child_lists keys
  end.

Fixpoint sorted_nat (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    match xs with
    | []      => true
    | y :: ys => Nat.leb x y && sorted_nat xs
    end
  end.


Definition check_btree_sorted (t : Tree nat) : bool :=
  sorted_nat (flatten_btree t).


Eval compute in check_btree_sorted btree_example.
(* = true : bool *)

Eval compute in check_btree_sorted bad_btree_example.
(* = false : bool *)




(*----------------------------------------------------------------------------------------*)

(* The btree is balanced *)
Fixpoint collect_leaf_depths (t : Tree nat) (current_depth : nat) : list nat :=
  match t with
  | Nil _=> [current_depth]
  | Leaf _ _ => [current_depth]
  | Node _ _ children =>
      flat_map (fun child => collect_leaf_depths child (S current_depth)) children
  end.

Definition is_btree_balanced (t : Tree nat) : bool :=
  all_equal (collect_leaf_depths t 0).

Compute is_btree_balanced btree_example.

(*-----------------------------------------------------------------------------------------*)

(* Combine all the checks into a single “is_btree” predicate. *)

Definition is_btree (m : nat) (t : Tree nat) : bool :=
  (* 1. Every node has at most m children. *)
  check_max_children m t
  && (* 2. Every non-root internal node has at least [m/2] children. *)
     check_min_children m t
  && (* 3. The root has at least two children (unless it is a leaf). *)
     check_root_children t
  && (* 4. All leaves are on the same level. *)
     check_all_leaves_same_level t
  && (* 5. Every non-leaf node with k children contains k−1 keys. *)
     valid_btree_children_key_relation t
  && (* 6. The in-order traversal of keys is strictly increasing. *)
     check_btree_sorted t
  && (* 7. The tree is balanced (all root-to-leaf paths have equal length). *)
     is_btree_balanced t.

(* Example evaluation on the given sample: *)

Eval compute in (is_btree 3 btree_example).  (* true for btree_example *)
Eval compute in (is_btree 3 bad_btree_example). (*false for bad_btree_example*)


(*-----------------------------------------------------------------------------------------*)


(* Search in a B-tree *)

Section BTreeSearch.
  Context {A : Type}.
  Context (cmp : A -> A -> comparison).

  (* search a sorted list of keys *)
  Fixpoint search_keys (keys : list A) (x : A) : bool :=
    match keys with
    | [] => false
    | k :: ks =>
      match cmp x k with
      | Eq => true (* hit the key *)
      | Lt => false (* x is smaller than this key, and keys are sorted ⇒ not here *)
      | Gt => search_keys ks x (* x is greater, keep scanning *)
      end
    end.

  (* search the whole tree *)
  Fixpoint search (t : Tree A) (x : A) : bool :=
    match t with
    | Nil _ =>
      false
    | Leaf _ keys =>
      search_keys keys x
    | Node _ keys children =>
      let fix aux (ks : list A) (cs : list (Tree A)) {struct cs} : bool :=
          match cs with
          | [] => false
          | c :: cs' =>
            match ks with
            | [] =>
              search c x
            | k :: ks' =>
              match cmp x k with
              | Eq => true
              | Lt => search c x
              | Gt => aux ks' cs'
              end
            end
          end
      in aux keys children
    end.

End BTreeSearch.

(*-----------------------------------------------------------------------------------------*)

Definition cmp_nat := Nat.compare.
Definition search_nat := @search nat cmp_nat.
Compute (search_nat btree_example 10).    (* = true *)
Compute (search_nat btree_example 50).    (* = true *)
Compute (search_nat btree_example 65).    (* = true *)
Compute (search_nat btree_example 100).   (* = true *)
Compute (search_nat btree_example 240).   (* = true *)

Compute (search_nat btree_example 7).     (* = false *)
Compute (search_nat btree_example 37).    (* = false *)
Compute (search_nat btree_example 175).   (* = false *)
Compute (search_nat btree_example 500).   (* = false *)


(*-----------------------------------------------------------------------------------------*)


Section BTreeInsert.
  Context {A : Type}.
  Context (cmp : A -> A -> comparison).
  Variable m : nat.
  Hypothesis m_ge_2 : 2 <= m.

  (* max number of keys allowed in one node *)
  Definition max_keys := 2*m - 1.

  Fixpoint tree_size {A} (t : Tree A) : nat :=
  match t with
  | Nil _       => 1
  | Leaf _ ks   => 1 + length ks
  | Node _ ks cs =>
    1 + length ks + fold_left (fun acc c => acc + tree_size c) cs 0
  end.

  (* test if a node is full *)
  Definition full (t : Tree A) : bool :=
    match t with
    | Nil _       => false
    | Leaf _ ks   => length ks =? max_keys
    | Node _ ks _ => length ks =? max_keys
    end.

  (* insert into a sorted list of keys *)
  Fixpoint insert_sorted (ks : list A) (x : A) : list A :=
    match ks with
    | []       => [x]
    | y :: ys =>
      match cmp x y with
      | Lt | Eq => x :: ks
      | Gt      => y :: insert_sorted ys x
      end
    end.

  (* replace the n-th child in a list of children *)
  Fixpoint replace_nth {B} (n : nat) (b : B) (ls : list B) : list B :=
    match n, ls with
    | _, []       => []
    | 0, _ :: xs  => b :: xs
    | S n', y::ys => y :: replace_nth n' b ys
    end.

  (* find the index of the first key satisfying predicate *)
  Fixpoint find_index {A'} (p : A' -> bool) (l : list A') (n : nat) : option nat :=
    match l with
    | [] => None
    | x :: xs => if p x then Some n else find_index p xs (S n)
    end.

  Definition find_index_start {A'} (p : A' -> bool) (l : list A') : option nat :=
    find_index p l 0.

  (* split a full leaf or node into a two-child node *)
  Definition split (t : Tree A) : Tree A :=
    match t with
    | Leaf _ ks =>
      let i := length ks / 2 in
      let L := firstn i ks in
      let R := skipn i ks in
      match R with
      | mid :: R' => Node m [mid] [Leaf m L; Leaf m R']
      | []        => Leaf m ks 
      end

    | Node _ ks cs =>
      let i   := length ks / 2 in
      let Lk  := firstn i ks in
      let Rk  := skipn i ks in
      let Lc  := firstn (i+1) cs in
      let Rc  := skipn (i+1) cs in
      match Rk, Lc, Rc with
      | mid::Rk', Lc', Rc' =>
        Node m [mid]
             [ Node m Lk  Lc'
             ; Node m Rk' Rc' ]
      | _,_,_ => Node m ks cs 
      end

    | Nil _ => t
    end.


  Fixpoint insert_non_full_aux (fuel : nat) (t : Tree A) (x : A) : Tree A :=
    match fuel with
    | 0 =>
      t

    | S fuel' =>
      match t with

      | Nil _ =>
        (* inserting into an empty (nil) tree just yields a one‐key leaf *)
        Leaf m [x]

      | Leaf _ ks =>
        let ks' := insert_sorted ks x in
        if length ks' <=? max_keys then
          Leaf m ks'
        else
          split (Leaf m ks')

      | Node _ ks cs =>
        (* Decide which child to recurse on. *)
        let idx := find_index_start
                     (fun k => match cmp x k with
                               | Lt => true
                               | Eq => true
                               | Gt => false
                               end) ks in
        let i :=
          match idx with
          | Some n => n
          | None   => length ks  (* go to the rightmost child, if x is larger than all keys *)
          end in

        (* c0 is the chosen child; if it’s full, split it first. *)
        let c0 := nth i cs (Leaf m []) in
        let c1 := if full c0 then split c0 else c0 in

        let c2 := insert_non_full_aux fuel' c1 x in

        (* Rebuild this node with the updated child. *)
        let rebuilt := Node m ks (replace_nth i c2 cs) in

        (* If the rebuilt node is now full, we split it at the top too. *)
        if full rebuilt then split rebuilt else rebuilt
      end
    end.

  Definition insert_non_full (t : Tree A) (x : A) : Tree A :=
    insert_non_full_aux (tree_size t) t x.

  (* Finally, the top‐level [insert] stays the same: if the root is full, split first. *)
  Definition insert (t : Tree A) (x : A) : Tree A :=
    if full t then insert_non_full (split t) x
              else insert_non_full t x.

End BTreeInsert.


(*-----------------------------------------------------------------------------------------*)


Eval compute in (
  let t' := @insert nat Nat.compare 3 btree_example 25 in
  is_btree 3 t'
).
(* true *)

Eval compute in (
  let t' := @insert nat Nat.compare 3 btree_example 5 in
  is_btree 3 t'
).
(* true *)

(*-----------------------------------------------------------------------------------------*)

