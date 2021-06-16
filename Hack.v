
Section Hack.
  Require Import Minus.
  Fail Fixpoint div (x y:nat) {struct x}: nat :=
    if Nat.eqb x 0
    then 0
    else  if Nat.eqb y 0
          then x
          else S (div (x-y) y).


  Lemma minus_smaller_S : forall x y:nat, x - y < S x. Admitted.
  Definition minus_decrease :
      forall x y:nat, Acc lt x ->
        x <> 0 ->
        y <> 0 ->
        Acc lt (x-y).
  Admitted.

  Definition div_aux (x y:nat) (H: Acc lt x) : nat.
    fix 3.
    intros.
    refine (if eq_nat_dec x 0
    then 0
    else if eq_nat_dec y 0
    then y
    else S( div_aux (x-y) y _)).

End Hack.
