Require Export Induction.
Module NatList.

  Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

  Check pair 3 5.

  Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Compute (fst (pair 3 5)).
(* ===> 3 *)

Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  (*simpl.*)
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(*Exercise: 1 star (snd_fst_is_swap)*)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(**Exercise: 1 star, optional (fst_swap_is_snd)*)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intro p.
  destruct p as [m n].
  simpl.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                       (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Compute length mylist1.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof.  reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(**Exercise: 2 stars, recommended (list_funs)
Complete the definitions of nonzeros, oddmembers and countoddmembers below. Have a look at the tests to understand what these functions should do.*)
Fixpoint nonzeros (l:natlist) : natlist  :=
  match l with
  | nil => nil
  | h :: t => match h with
              | O => nonzeros t
              | S n => [h] ++ nonzeros t
               end
  end.
              
              
Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  simpl.
  reflexivity.
Qed.

Compute oddb 4. (*Tests whether a number is odd*)

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match oddb h with
             | true => [h] ++ oddmembers t
             | false => oddmembers t
             end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  simpl.
  reflexivity.
Qed.

Definition countoddmembers (l:natlist) : nat :=
  match oddmembers l with
  |nil => 0
  |h :: t => 1 + length t
  end.

Compute countoddmembers [1;0;3;1;4;5;7;2;2;5].

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  reflexivity.
Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
reflexivity.
  Qed.
  
Example test_countoddmembers3:
  countoddmembers nil = 0.
reflexivity.
  Qed.