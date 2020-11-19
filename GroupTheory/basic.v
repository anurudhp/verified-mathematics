Require Import Group.

Theorem id_op_id_eq_id : forall G op id (g : Group G op id), op id id = id.
Proof.
  intros.
  destruct g as [_ id_eqn].
  destruct (id_eqn id).
  assumption.
Qed.

Theorem id_unique :
  forall G op id1 id2
    (g1 : Group G op id1)
    (g2 : Group G op id2),
    id1 = id2.
Proof.
  intros G op id1 id2 [_ eqn1] [_ eqn2].
  destruct (eqn1 id2) as [_ H1].
  destruct (eqn2 id1) as [H2 _].
  rewrite H1 in H2.
  auto.
Qed.
