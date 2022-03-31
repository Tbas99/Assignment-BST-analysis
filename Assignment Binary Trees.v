(**
  Standard Assignment:  Binary Tree Analysis
  Made by:              Tobias Sagis & Luuk Spierings
**)

(* Libraries to import *)
Require Import Lia.

(* Define a tree type *)
Inductive tree : Set :=
  | leaf : tree
  | node : tree -> nat -> tree -> tree.

Check node (node (node leaf 2 leaf) 5 (node leaf 7 leaf)) 10 (node (node leaf 12 leaf) 16 (node leaf 17 leaf)).

(*
  Before we define the predicate we need some helper function in
  order to establish the validity of the binary search tree properties.
  With this we take a predicate P and check if it holds on all subtree's
  by inductively traversing the subtree's.
*)
Fixpoint bst_prop (P : nat -> tree -> Prop) (T : tree) : Prop :=
  match T with
  | leaf => True (* A leaf trivially satisfies the bst property *)
  | node l n r => P n T /\ bst_prop P l /\ bst_prop P r
  end.

(*
    Define the predicate on tree to express that a tree is sorted.
    With this we mean that the tree is actually a sorted binary tree,
    or simply a binary search tree.
    For a tree to be a binary search tree it must hold that for all
    internal nodes:
    - The key stored must be greater than all the keys in the node's
      left subtree.
    - The key stored must be less than or equal all the keys in the
      node's right subtree.
*)
Fixpoint bst (T : tree) : Prop :=
  match T with
  | leaf => True
  | node l n r => (bst_prop (fun x _ => x < n) l) /\ (bst_prop (fun x _ => (x > n) \/ (x = n)) r) /\ bst l /\ bst r
  end.

(* Check if bst classification is correct *)
Section verify_bst_invariant.

Definition invalid_bst_tree : Prop :=
  bst (node (node leaf 6 leaf) 4 (node leaf 10 leaf)).

Definition valid_bst_tree : Prop :=
  bst (node (node leaf 4 leaf) 6 (node leaf 10 leaf)).

Theorem is_not_bst_tree : ~invalid_bst_tree.
Proof.
unfold invalid_bst_tree.
simpl.
lia.
Qed.

Theorem is_bst_tree : valid_bst_tree.
unfold valid_bst_tree.
simpl.
lia.
Qed.

End verify_bst_invariant.

(*
  Define a function that takes a binary search tree and a 
  natural number and inserts the number in the right place
  in the tree.
  So that the insertion does not break the binary search tree
  property.
*)
Fixpoint insert (N : nat) (T : tree ) : tree :=
  match T with
  | 
  end.





