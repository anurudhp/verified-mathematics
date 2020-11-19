Class Group (G : Set) (op : G -> G -> G) (id : G) :=
  {  assoc : forall x y z, op x (op y z) = op (op x y) z;
     id_eqn : forall x, op x id = x /\ op id x = x
  }.

