Require Export Basics.

Theorem plus_n_O_firsttry : forall n:nat,
    n = n + 0.

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

(*Exercise: 2 stars, recommended (basic_induction)
Prove the following using induction. You might need previously proven results.*)

(*
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  destruct n.
  -
    simpl.
    reflexivity.
  -
    simpl.
    induction n as [|n' IHn].
    +
      simpl.
      reflexivity.
    +
      simpl.
      assumption.
Qed.*)

Theorem mult_0_r : forall n:nat,
    n * 0 = 0.
Proof.
  intros n.
  induction n as [|n' IHn].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHn.
    reflexivity.    
Qed.
  
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' Sn].
  - 
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> Sn.
    reflexivity.
Qed.

(*Auxiliar Theorem*)
Theorem plus_n_0 : forall n: nat, n + 0 = n.
Proof.
  intros n.
  simpl.
  induction n as [|n' IHn].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHn.
    reflexivity.
  
  Qed.

(*Auxiliar Theorem*)
Theorem plus_n_m_n_plus_Sn : forall n m: nat, S(n + m) = n + S m.
Proof.
  intros n m.
  induction n as [|n' IHn].
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite <- IHn.
    reflexivity.
Qed.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n.
  +
    rewrite <- plus_n_O.
    simpl.
    reflexivity.
  +
    simpl. 
    rewrite -> IHn.    
    rewrite <- plus_n_m_n_plus_Sn.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.

  intros n m p.
  induction n as [|n' IHn].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite <- IHn.
    reflexivity.
Qed.

(*Exercise: 2 stars (double_plus)
Consider the following function, which doubles its argument:*)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(*Use induction to prove this simple fact about double:*)
Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n as [|n' IHn'].
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_m_n_plus_Sn.
    reflexivity.
Qed.

(*Auxiliar for exercise below*)
Theorem negb_negb_b : forall b : bool, negb (negb b) = b.
Proof.
  intro b.
  destruct b.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
Qed.


(*Exercise: 2 stars, optional (evenb_S)
One inconvenient aspect of our definition of evenb n is the recursive call on n - 2. This makes proofs about evenb n harder when done by induction on n, since we may need an induction hypothesis about n - 2. The following lemma gives an alternative characterization of evenb (S n) that works better with induction:*)
Theorem evenb_S : forall n : nat, evenb (S n) = negb (evenb n).
Proof.
  intro n.
  simpl.
  induction n.
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite -> IHn.
    rewrite -> negb_negb_b.
    reflexivity.
   
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { simpl. reflexivity. }(*"Simpl" added by me*)
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
       simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

(*Exercise: 2 stars, optional (beq_nat_refl_informal)
Write an informal proof of the following theorem, using the informal proof of plus_assoc as a model. Don't just paraphrase the Coq tactics into English!*)
Theorem beq_nat_refl_informal: forall n : nat, beq_nat n n = true.
Proof.

  intro n.
  induction n as [|n' IHn].
  -
    simpl.
    reflexivity.
  -
    simpl.
    (*assumption.*)
    (*apply IHn.*)
    rewrite <- IHn.
    reflexivity.
Qed.

(*My simpler beq_nat*)
Fixpoint beq_nat_easy (n m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S n, S m => beq_nat_easy n m
  | _, _ => false
  end.

(*My new - and personal - version of the theorem*)
Theorem beq_nat_refl_informal_easy: forall n : nat, beq_nat_easy n n = true.
Proof.

  intro n.
  induction n as [|n' IHn].
  -
    simpl.
    reflexivity.
  -
    simpl.
    (*assumption.*)
    (*apply IHn.*)
    rewrite <- IHn.
    reflexivity.
Qed.