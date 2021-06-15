let () = print_endline "Hello, World!"

module TestDemo = struct
  open Test

  let rec nat_of_int n =
    if n <= 0 then O else S (nat_of_int (n-1))

  let int_of_nat =
    let rec helper acc = function
    | O -> acc
    | S p -> helper (1+acc) p
  in
  helper 0

  let () =
    let a = 52 in
    let b = 3 in
    let Divex (q,r) = eucl_dev (nat_of_int b) (nat_of_int a) in

    Format.printf "%d / %d = %d (and %d)\n%!" a b (int_of_nat q) (int_of_nat r)
end


module TestCo = struct
  open TestCo

  let x = Nil
end
