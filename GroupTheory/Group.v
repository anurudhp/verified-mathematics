Class Semigroup (G : Set) (op : G -> G -> G) :=
  {  Semigroup_assoc : forall x y z, op x (op y z) = op (op x y) z
  }.

Class Monoid (G : Set) (op : G -> G -> G) (id : G) :=
  {  Monoid_Semigroup : Semigroup G op
  ;  Monoid_id_eqn : forall x, op x id = x /\ op id x = x
  }.

Class Group (G: Set) (op : G -> G -> G) (id : G) :=
  {  Group_Monoid : Monoid G op id
  ;  Group_inv_exists : forall x, exists y, op x y = id /\ op y x = id
  }.
