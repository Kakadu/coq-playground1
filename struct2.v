(* https://stackoverflow.com/questions/55704472/structural-recursion-on-two-arguments *)
Require Import Program Omega.

Inductive tuple_lt : (nat * nat) -> (nat * nat) -> Prop :=
  fst_lt : forall a b c d, a < c -> tuple_lt (a, b) (c, d).

Program Fixpoint f (a : nat) (b : nat) {measure (a, b) (tuple_lt)} :=
match a with
| 0 => 0
| S n => f n b
end.

Next Obligation.
apply fst_lt. auto.
Qed.

Lemma tuple_lt_wf : well_founded tuple_lt.
Proof.
  apply well_founded_lt_compat with fst.
  intros ? ? []; assumption.
Defined.

Next Obligation.
apply measure_wf. apply tuple_lt_wf.
Defined.
