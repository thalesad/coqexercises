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
  apply plus_n_O.
  simpl.
  rewrite -> IHn.
  apply plus_n_m_n_plus_Sn.
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