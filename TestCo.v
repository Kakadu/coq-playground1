From Coq Require Export String.
(* Require to fix errors like `No interpretation for string "1"` *)
Open Scope string_scope.
From Coq Require Export Nat.
From Coq Require Export List.
Import ListNotations.

Require Extraction.
(* export string as char list. Not idea how to do it properly *)
From Coq  Require ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Check (Some 1).

Section listAssoc.
  Variable A: Type.
  Fixpoint find  (xs: list (string * A)) (k: string) : option A :=
    match xs with
    | [] => None
    | (h,v) :: tl => if String.eqb h k then Some v else find tl k
    end.
End listAssoc.
Search "find".

Check eq_refl : None = find string [] "1".
Check eq_refl : (Some O) = find nat [ ("1", O) ] "1".



Section unif.
  Inductive term :=
  | Var : string -> term
  | EInt : nat -> term
  | ENil : term
  | ECons : term -> term -> term.

  Inductive subst := Subst : list (string * term) -> subst.

  Definition empty_subst := (Subst []).

  Fixpoint walk (v: term) (s: subst): term :=
    match v with
    | EInt _ => v
    | ENil => v
    | ECons l r => ECons (walk l s) (walk r s)
    | Var s => Var s
    end.

  Definition extend s k v :=
    match s with
    | Subst ss => Subst ( (k,v) :: ss)
    end.

  Definition unify_helper x y (acc: option subst) :=
    match acc with
    | None => None
    | Some s =>
      match walk x s, walk y s with
      | (Var sx), (Var sy) =>
          if String.eqb sx sy
          then acc
          else Some (extend s sx (Var sy))
      | r, (Var sx) => Some (extend s sx r)
      | (Var sx), r => Some (extend s sx r)
      | EInt l, EInt r =>
          if Nat.eqb l r then acc else None
      | EInt _, ECons _ _
      | ECons _ _, EInt _
      | ENil, _ | _, ENil
      | ECons _ _, _  => None
      end
    end.

  Definition unify x y := unify_helper x y None.

End unif.
(* Extraction "TestCo.ml" term. *)


Section stream2.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream
  | Delay : stream -> stream
  | Nil : stream
  .

  (* https://www.labri.fr/perso/casteran/RecTutorial.pdf *)
  Print Acc.

  Fail CoFixpoint mplus (l r: stream)  : stream :=
    match l with
    | Nil => r
    | Cons h tl => Cons h (mplus r tl)
    | Delay old => mplus r old
    end.

  Fail CoFixpoint mplus (l r: stream) : stream :=
    match l with
    | Nil => r
    | Cons h tl => Cons h (mplus r tl)
    | Delay old =>
        match r with
        | Nil => old
        | Cons h tl => Cons h (mplus old tl)
        | Delay old2 => mplus old old2
        end
    end.

End stream2.

Section MK.




End MK.


(* Extraction "TestCo.ml" stream term unify. *)
