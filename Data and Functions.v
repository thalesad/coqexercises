
(*Exercise: 1 star (nandb)*)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => negb(b2)
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(*Exercise: 1 star (andb3)*)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | false => false
  | true => andb b2 b3
  end.

Print andb3.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check negb. (*show the function type*)

(*Creates an alternative way to represent natural numbers*)
Module NatPlayground.
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.

  Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') =>  n'
  end.
Compute (minustwo 4).
Check S.
Check pred.
Check minustwo.

(*Executes and print the result of a function*)
Compute pred 2.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).
Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
  
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(*Exercise: 1 star (factorial)*)
(**Recall the standard mathematical factorial function:
       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)
Translate this into Coq.*)
Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => mult (S n') (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
  Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(*Exercise: 1 star (blt_nat)
The blt_nat function tests natural numbers for less-than, yielding a boolean. Instead of making up a new Fixpoint for this one, define it in terms of a previously defined function.*)
Definition blt_nat (n m : nat) : bool :=
  match beq_nat n m with
      | true => false
      | false => leb n m
  end.
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(*Exercise: 1 star (factorial)
Recall the standard mathematical factorial function:
       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)
Translate this into Coq.*)

(*Fixpoint factorial2 (n:nat) : nat :=
  match n with
  |0 => 1
  |S n => n * factorial2 (n)
  end.

Example test_factorial3: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial4: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.*)

(*Proof by Simplification*)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed. (*remove simpl. to go straighforward*)
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity. Qed. (*remove simpl. to go straighforward*)

(*Proof by rewriting*)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

  Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity. Qed.

(*Exercise: 1 star (plus_id_exercise)
Remove "Admitted." and fill in the proof.*)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros a b c. (*ou intros n m o*)
  intros H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

(*Exercise: 2 stars (mult_S_1)*)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros Hm.
  simpl.
  rewrite <- Hm. (*destruct Hm.*)
  reflexivity.
   Qed.
  (* (N.b. This proof can actually be completed with tactics other than
     rewrite, but please do use rewrite for the sake of the exercise.) *)

(*Proof by Case Analysis*)
Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(*Below, I present three ways to solve the same exercise*)
(*Exercise: 2 stars (andb_true_elim2)
Prove the following claim, marking cases (and subcases) with bullets when you use destruct.*)
Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof.

  intros b c.
  destruct b.
  {
    destruct c.
    {
      reflexivity.
    }
    {
      intros Htft.
      rewrite <- Htft.
      simpl.
      reflexivity.
    }
  }

  {
    destruct c.
    {
      intros Hftt.
      reflexivity.
    }

    {
      intros Hfft.
      rewrite <- Hfft.
      simpl.
      reflexivity.
    }
  }
Qed.

(*Exercise: 2 stars (andb_true_elim2)
Prove the following claim, marking cases (and subcases) with bullets when you use destruct.*)
(*Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof.
  intros [] [].
  - reflexivity.
  - intros Hbt.
    +rewrite <- Hbt.
     simpl.
     reflexivity.
  - reflexivity.
  - intros Hfft.
    + rewrite <- Hfft.
      simpl.
      reflexivity.    
Qed.*)

(*Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof.
  intros b.
  intros c.
  destruct b.
  {
    destruct c.
    {
      reflexivity.
    }
    {
    intros Htft.
    rewrite <- Htft.
    simpl.
    reflexivity.
    }
  }
  destruct c.
  {
    reflexivity.
  }
  intros Hfft.
  rewrite <- Hfft.
  simpl.
  reflexivity.
  Qed.*)

(*Exercise: 1 star (zero_nbeq_plus_1)*)
Theorem zero_nbeq_plus_1 :forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [|n].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    reflexivity.
  }
Qed.