
Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream
  | Delay : stream -> stream
  | Nil : stream
  .

End stream.
Require Extraction.
Extraction "TestCo.ml" stream.
