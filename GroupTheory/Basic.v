Require Import Math.GroupTheory.Group.

(* id * id = id *)
Theorem id_op_id_eq_id : forall G op id (g : Monoid G op id), op id id = id.
Proof.
  intros.
  destruct g as [_ id_eqn].
  destruct (id_eqn id).
  assumption.
Qed.

(* Identity of a Monoid is unique *)
Theorem id_unique :
  forall G op id1 id2
    (g1 : Monoid G op id1)
    (g2 : Monoid G op id2),
    id1 = id2.
Proof.
  intros G op id1 id2 [_ eqn1] [_ eqn2].
  destruct (eqn1 id2) as [_ H1].
  destruct (eqn2 id1) as [H2 _].
  rewrite H1 in H2.
  auto.
Qed.

Theorem group_left_cancel :
  forall G op id (g : Group G op id) x y z,
    op x y = op x z -> y = z.
Proof.
  intros.
  destruct g as [[[Hassoc] Hid] Hinv].
  destruct (Hinv x) as [x' [Hxx' Hx'x]].
  assert (op x' (op x y) = op x' (op x z)) as H1 by (rewrite H; reflexivity).
  rewrite (Hassoc x' x y) in H1.
  rewrite (Hassoc x' x z) in H1.
  rewrite Hx'x in H1.
  assert (op id y = y) as Hy by (destruct (Hid y); auto).
  assert (op id z = z) as Hz by (destruct (Hid z); auto).
  rewrite <- Hy, <- Hz.
  exact H1.
Qed.

Lemma inverse_commute : forall G op id (g : Group G op id) x y, op x y = id -> op y x = id.
Proof.
  intros.
  pose proof (group_left_cancel G op id g) as Hcancel.
  destruct g as [[[Hassoc] Hid] Hinv].
  apply (Hcancel x).
  rewrite Hassoc.
  rewrite H.
  destruct (Hid x).
  rewrite H0, H1.
  reflexivity.
Qed.

(* Inverse of any group element is unique *)
Theorem inverse_unique:
  forall G op id (g: Group G op id) (x y1 y2 : G),
    op x y1 = id -> op x y2 = id -> y1 = y2.
Proof.
  intros G op id g x y1 y2 E1 E2.
  assert (op y1 x = id) as H1. {
    apply inverse_commute; auto.
  }
  assert (op y2 x = id) as H2. {
    apply inverse_commute; auto.
  }
  destruct g as [[[Hassoc] Hid] Hinv].
  specialize (Hassoc y1 x y2).
  rewrite E2 in Hassoc.
  rewrite H1 in Hassoc.
  destruct (Hid y1) as [Hy1 _].
  destruct (Hid y2) as [_ Hy2].
  rewrite <- Hy1, <- Hy2.
  exact Hassoc.
Qed.
