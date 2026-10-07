(* meanders_ox [N] [--from M] [--threads T] [--two-moduli] [--check]: print Arnold's numbers
   (OEIS A005316) for n = M..N, computed by the parallel transfer matrix. *)

let () =
  (* The big tables are unboxed arrays the GC never scans, so a major cycle is cheap; run
     them often (space_overhead 30 instead of 120) so that freed tables return to the
     allocator soon, which keeps the peak footprint down. Setting OCAMLRUNPARAM at all
     leaves the GC parameters to it. *)
  if Option.is_none (Sys.getenv_opt "OCAMLRUNPARAM")
  then Gc.set { (Gc.get ()) with space_overhead = 30 };
  let args = Array.to_list Sys.argv |> List.tl in
  let rec flag name = function
    | a :: v :: _ when a = name -> int_of_string_opt v
    | _ :: rest -> flag name rest
    | [] -> None
  in
  let n =
    match args with
    | a :: _ -> Option.value (int_of_string_opt a) ~default:32
    | [] -> 32
  in
  let from = Option.value (flag "--from" args) ~default:0 in
  let threads =
    Option.value (flag "--threads" args) ~default:(Domain.recommended_domain_count ())
  in
  let two = List.mem "--two-moduli" args in
  let check = List.mem "--check" args in
  Printf.printf "# n\tcount\tpeak_states\ttotal_states\tseconds\tthreads=%d\n%!" threads;
  Parallel_scheduler.with_parallel ~max_workers:threads (fun par ->
    for m = from to n do
      let t0 = Unix.gettimeofday () in
      let s = Meanders.count par ~m ~threads ~two_moduli:two in
      let secs = Unix.gettimeofday () -. t0 in
      if check
      then (
        let c = Meanders.Crt.unsigned_to_string (Meanders.Serial.count m) in
        if c <> s.count
        then failwith (Printf.sprintf "parallel and serial disagree at n = %d" m));
      Printf.printf
        "%d\t%s\t%d\t%d\t%.3f\n%!"
        m
        s.count
        s.peak_states
        s.total_states
        secs
    done)
;;

let () =
  if Sys.getenv_opt "MEANDERS_GC" <> None
  then (
    let s = Gc.quick_stat () in
    Printf.eprintf
      "minor_collections=%d major_collections=%d minor_words=%.0f major_words=%.0f \
       compactions=%d heap_words=%d top_heap_words=%d\n"
      s.minor_collections
      s.major_collections
      s.minor_words
      s.major_words
      s.compactions
      s.heap_words
      s.top_heap_words)
;;
