Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Definition peirce := forall P Q : Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P : Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q : Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q : Prop,
  (P -> Q) -> (~P \/ Q).

Theorem excluded_middle_2_peirce :
  excluded_middle -> peirce.
Proof.
  unfold excluded_middle.
  unfold peirce.
  intros Hem P Q H.
  assert (P \/ ~ P) as H1.
  { apply Hem. }
  destruct H1 as [H1 | H1].
  - apply H1.
  - apply H.
    intros HP.
    apply H1 in HP.
    destruct HP.
Qed.

Theorem peirce_2_double_negation_elimination :
  peirce -> double_negation_elimination.
Proof.
  unfold peirce.
  unfold double_negation_elimination.
  intros Hpc P HP.
  unfold not in HP.
  assert (False -> P) as HFP.
  { intros con. destruct con. }
  assert ((P -> False) -> P) as HPFP.
  { intros HPF.
    apply HFP.
    apply HP.
    apply HPF. }
  apply Hpc in HPFP.
  apply HPFP.
Qed.

Theorem double_negation_elimination_2_de_morgan_not_and_not :
  double_negation_elimination -> de_morgan_not_and_not.
Proof.
  unfold double_negation_elimination.
  unfold de_morgan_not_and_not.
  intros Hdne P Q H.
  apply (Hdne (P \/ Q)).
  unfold not in H. unfold not.
  intros HPQ.
  apply H.
  split.
  - intros HP.
    apply HPQ.
    left. apply HP.
  - intros HQ.
    apply HPQ.
    right. apply HQ.
Qed.

Theorem de_morgan_not_and_not_2_implies_to_or :
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not.
  unfold implies_to_or.
  intros Hdmnan P Q H.
  apply Hdmnan.
  unfold not.
  intros [H1 H2].
  apply H1.
  intros HP.
  destruct H2.
  apply H.
  apply HP.
Qed.

Theorem implies_to_or_2_excluded_middle :
  implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or.
  unfold excluded_middle.
  intros Hito P.
  apply or_comm.
  apply (Hito P P).
  intros HP.
  apply HP.
Qed.
