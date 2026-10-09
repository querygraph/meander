(* meanders_ox [N] [--from M] [--threads T] [--two-moduli] [--check]: print Arnold's numbers
   (OEIS A005316) for n = M..N, computed by the parallel transfer matrix.

   meanders_ox --mitm B: every A(n), n <= B, by meet in the middle, each checked by a second
   split. meanders_ox --store DIR --horizon B [--mem-gb G | --cap N]: create or extend the
   persistent meet-in-the-middle store in DIR to horizon B; [--discard] deletes each backward
   layer once used (the store then cannot be extended), [--min-free-gb G] pauses when the disk
   has less free space, [--passes P] builds each step in P passes over its source ([auto]:
   enough passes per step to avoid spilling; default 1). A file PAUSE in DIR pauses at the next layer boundary (exit code 3);
   the same command resumes. *)

(* MEANDERS_GC=1: print GC statistics at exit. *)
let () =
  if Sys.getenv_opt "MEANDERS_GC" <> None
  then
    at_exit (fun () ->
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


let () =
  (* The big tables are unboxed arrays the GC never scans, so a major cycle is cheap; run
     them often (space_overhead 30 instead of 120) so that freed tables return to the
     allocator soon, which keeps the peak footprint down. Setting OCAMLRUNPARAM at all
     leaves the GC parameters to it. *)
  let args = Array.to_list Sys.argv |> List.tl in
  (* The store churns through a full set of shard tables per layer: collect more eagerly
     still (10: 7.3 GB instead of 8.1 GB at horizon 46, at the same speed). *)
  if Option.is_none (Sys.getenv_opt "OCAMLRUNPARAM")
  then
    Gc.set
      { (Gc.get ()) with space_overhead = (if List.mem "--store" args then 10 else 30) };
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
  let rec arg name = function
    | a :: v :: _ when a = name -> Some v
    | _ :: rest -> arg name rest
    | [] -> None
  in
  (match arg "--store" args, flag "--horizon" args with
   | Some root, Some b ->
     let cap =
       match flag "--cap" args with
       | Some c -> c
       | None ->
         let gb =
           Option.value (Option.bind (arg "--mem-gb" args) float_of_string_opt) ~default:16.0
         in
         max 1024 (int_of_float (gb *. 1e9 /. (4096.0 *. 120.0)))
     in
     let discard = List.mem "--discard" args in
     let min_free =
       match Option.bind (arg "--min-free-gb" args) float_of_string_opt with
       | Some g -> int_of_float (g *. 1e9)
       | None -> 0
     in
     let outcome =
       Parallel_scheduler.with_parallel ~max_workers:threads (fun par ->
         Meanders.Store.extend
           par
           ~discard
           ~min_free
           ~passes:
             (match arg "--passes" args with
              | Some "auto" -> 0
              | Some v -> int_of_string v
              | None -> 1)
           ~root
           ~target:b
           ~threads
           ~cap
           ~out:(fun line ->
             print_endline line;
             flush stdout)
           ())
     in
     (* 3: paused (PAUSE file or low disk); run again with the same horizon to resume *)
     exit (match outcome with Complete -> 0 | Paused -> 3)
   | _ -> ());
  (match flag "--mitm" args with
   | Some b ->
     let t0 = Unix.gettimeofday () in
     Printf.printf
       "# n\tcount\tcheck\tforward_states\tbackward_states\tthreads=%d\n%!"
       threads;
     let rows =
       Parallel_scheduler.with_parallel ~max_workers:threads (fun par ->
         Meanders.Mitm.run par ~horizon:b ~threads)
     in
     Array.iter
       (fun (r : Meanders.Mitm.row) ->
         let check =
           match r.check with
           | Some c when c = r.count -> "ok"
           | Some c -> Printf.sprintf "MISMATCH(%s)" c
           | None -> "-"
         in
         Printf.printf
           "%d\t%s\t%s\t%d\t%d\n"
           r.n
           r.count
           check
           r.forward_states
           r.backward_states)
       rows;
     Printf.eprintf "seconds: %.3f\n" (Unix.gettimeofday () -. t0);
     exit 0
   | None -> ());
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

