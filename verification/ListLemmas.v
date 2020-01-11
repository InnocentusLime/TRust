Require List.

Theorem map_skip_swap : forall (A B : Type) (l : list A) (f : A -> B) (n : nat),
    List.skipn n (List.map f l) = List.map f (List.skipn n l)
.
Proof.
    intros A B l.
    induction l.

    simpl.
    intros; destruct n.
    easy.
    easy.

    intros; destruct n.
    easy.
    simpl.
    apply IHl.
Qed.

Theorem list_firstn_skipn_eqn : forall (A : Type) (l : list A) (n : nat),
    l = (List.firstn (S n) l ++ List.skipn (S n) l)%list
.
Proof.
    intros A l.
    induction l.
    easy.
    simpl.
    intro n; destruct n.
    simpl.
    reflexivity.
    now rewrite <- IHl.
Qed.