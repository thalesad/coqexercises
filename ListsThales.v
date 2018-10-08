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

(**Exercise: 3 stars, advanced (alternate)
Complete the definition of alternate, which "zips up" two lists into one, alternating between elements taken from the first list and elements from the second. See the tests below for more specific examples.
Note: one natural and elegant way of writing alternate will fail to satisfy Coq's requirement that all Fixpoint definitions be "obviously terminating." If you find yourself in this rut, look for a slightly more verbose solution that considers elements of both lists at the same time. (One possible solution requires defining a new kind of pairs, but this is not the only way.)*)

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1 with
    |nil => l2
    |h :: t => match l2 with
               | nil => l1
               | a :: b => [h] ++ [a] ++ alternate t b
               end
    end.

Compute alternate [] [20;30].
  
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
simpl.
reflexivity.
Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
simpl.
reflexivity.
  Qed.
  
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
simpl.
reflexivity.
  Qed.
  
Example test_alternate4:
  alternate [] [20;30] = [20;30].
simpl.
reflexivity.
  Qed.

  Definition bag := natlist.

  (**Exercise: 3 stars, recommended (bag_functions)
Complete the following definitions for the functions count, sum, add, and member for bags.*)
Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => if beq_nat v h then 1 + count v t else count v t
  end.

Compute count 1 [1;2;3;1;4;1].
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
simpl.
reflexivity.
  Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
simpl.
reflexivity.
  Qed.

  Definition sum : bag -> bag -> bag :=
    app. (*or alternate*)

   Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
   simpl.
   reflexivity.
   Qed.

  (**Another way of implementing sum using anonymouys function*)
(** Definition sum : bag -> bag -> bag :=
    fun x y =>
      match x,y with
      | [], y => y
      | x, [] => x
      | x, y => x ++ y
      end.*)

  Definition add (v:nat) (s:bag) : bag :=
    match s with
    | nil => [v]
    | h :: t => [v] ++ s
  end.

  Compute add 1 [1;4;1].

  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  simpl.
  reflexivity.
  Qed.

  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  simpl.
  reflexivity.
  Qed.

  Definition member (v:nat) (s:bag) : bool :=
    match count v s with
    | 0 => false
    | _ => true
    end.
  

  (**Fixpoint member (v:nat) (s:bag) : bool :=
    match s with
    | nil => false
    | h :: t => if beq_nat h v then true else member  v t 
    end.*)

  Example test_member1: member 1 [1;4;1] = true.
  simpl.
  reflexivity.
  Qed.
  
  Example test_member2: member 2 [1;4;1] = false.
  simpl.
  reflexivity.
  Qed.

  Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t => if beq_nat h v then t else [h] ++ remove_one v t
    end.

  Compute remove_one 2 [2;3;5;3;2;7].

  Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  simpl.
  reflexivity.
  Qed.
  
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
simpl.
reflexivity.
Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
simpl.
reflexivity.
  Qed.

  
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
simpl.
reflexivity.
  Qed.

  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t => if beq_nat h v then remove_all v t else [h] ++ remove_all v t
    end.

  Compute remove_all 5 [5;5;5;2;7;2;1;5;4;5;1;5;4].

  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  simpl.
  reflexivity.
  Qed.
  
  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  simpl.
  reflexivity.
  Qed.
  
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
simpl.
reflexivity.
  Qed.
  
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
simpl.
  reflexivity.
  Qed.

  Fixpoint subset (s1:bag) (s2:bag) : bool :=
    match s1, s2 with
    | nil, _ => true (**nil is subset of anything*)
    | _, nil => false (**nothing is subset of nil*)
    | h :: t, s2 => if member h s2 then subset t (remove_one h s2) else false   
    end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
simpl.
reflexivity.
  Qed.
  
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
simpl.
reflexivity.
  Qed.

Theorem bag_theorem : forall (l: bag) (x: nat), length( add (count x l) l ) = length (add x l).
Proof.
  intros l x.
  induction l.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. simpl. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = cons n l' *)
    simpl.
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl.
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. simpl. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. simpl. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l =  *)
    simpl.
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl.
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'. reflexivity. Qed.

Search rev.

(**List Exercises, Part 1*)
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [| n l' IHl].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHl.
    reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| n l IHl].
  -
    simpl.
    rewrite -> app_nil_r.
    reflexivity.
  -
    simpl.
    rewrite -> IHl.
    Search app.
    rewrite -> app_assoc.
    reflexivity.
Qed.

Search app.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intro l.
  induction l as [| n l' IHl].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> rev_app_distr.
    simpl.
    rewrite -> IHl.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  induction l1 as [|n l' IHl].
  -
    simpl.
    rewrite -> app_assoc.
    reflexivity.
  -
    simpl.
    rewrite -> IHl.
    reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [|n l' IHl].
  -
    simpl.
    reflexivity.
  -
    Search nonzeros.
    induction n.
    +
      simpl.
      rewrite -> IHl.
      reflexivity.
    +
      simpl.
      rewrite IHl.
      reflexivity.
Qed.

Search count.

(**Auxiliar Fixpoint for Definition member_nat*)
Fixpoint count_nat (v:nat) (s:natlist) : nat :=
  match s with
  | nil => 0
  | h :: t => if beq_nat v h then 1 + count_nat v t else count_nat v t
  end.

(**Auxiliar Definition for Fixpoint beq_natlist*)
Definition member_nat (v:nat) (s:natlist) : bool :=
      match count_nat v s with
    | 0 => false
    | _ => true
    end.


Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | h::t, d::l =>  if beq_nat h d then beq_natlist t l else false
  end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
simpl.
reflexivity.
  Qed.

  Example test_beq_natlist2 :
    beq_natlist [1;2;3] [1;2;3] = true.
  simpl.
  reflexivity.

  Example test_beq_natlist3 :
    beq_natlist [1;2;3] [1;2;4] = false.
  simpl.
  reflexivity.

  Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intro l.
  induction l as [|n].
  -
    simpl.
    reflexivity.
  -
    rewrite -> IHl.
    induction n.
    +
      simpl.
      reflexivity.
    +
      rewrite -> IHn.
      reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  intro l.
  induction l as [|n IHl].
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.

(**The following lemma about leb might help you in the next exercise.*)
Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

(**Exercise: 3 stars, advanced (remove_does_not_increase_count)*)
Theorem remove_does_not_increase_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s.
  induction s as [|n].
  -
    simpl.
    reflexivity.
  -
    rewrite <- IHs.
    induction n.
    +
      simpl.
      rewrite -> ble_n_Sn.
      rewrite -> IHs.
      reflexivity.
    +
      simpl.
      reflexivity.
Qed.
