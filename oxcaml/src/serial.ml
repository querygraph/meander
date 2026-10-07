(* A plain sequential sweep with a stdlib [Hashtbl], counts modulo 2^63: the reference that
   [--check] compares the parallel sweep against. *)

let count m =
  let layer = ref (Hashtbl.create 16) in
  Hashtbl.replace !layer Word.init 1;
  for x = 0 to m do
    let next = Hashtbl.create (2 * Hashtbl.length !layer + 16) in
    Hashtbl.iter
      (fun k c ->
        let add k2 =
          if k2 >= 0
          then (
            match Hashtbl.find_opt next k2 with
            | Some c2 -> Hashtbl.replace next k2 (c + c2)
            | None -> Hashtbl.replace next k2 c)
        in
        let #(s0, s1, s2, s3) = Word.successors m x k in
        add s0;
        add s1;
        add s2;
        add s3)
      !layer;
    layer := next
  done;
  Option.value (Hashtbl.find_opt !layer Word.final) ~default:0
;;
