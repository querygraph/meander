(* Tests of the meet-in-the-middle modes:

   - the inverse step: on every state reachable within [depth_limit] bridges, [t] is a
     predecessor of [s] exactly when [s] is a bridge successor of [t]; [depth] is the first
     layer where a state appears; the packed [Back.predecessors] equals the slow reference on
     decoded words, with no duplicates, and its depth window filters exactly;
   - the in-memory driver against OEIS A005316, every second split agreeing;
   - the store's radix sort;
   - the store: built 16 -> 20 -> 24 (with tiny tables, so that every layer spills) it holds the
     same [values] file as one built directly at 24, and every value is right. *)

open Meanders

let expected =
  [| "1"; "1"; "1"; "2"; "3"; "8"; "14"; "42"; "81"; "262"; "538"; "1828"; "3926"; "13820"
   ; "30694"; "110954"; "252939"; "933458"; "2172830"; "8152860"; "19304190"; "73424650"
   ; "176343390"; "678390116"; "1649008456"; "6405031050"; "15730575554"; "61606881612"
   ; "152663683494"; "602188541928"; "1503962954930"
  |]
;;

let fail fmt = Printf.ksprintf failwith fmt
let depth_limit = 14

(* Bridge successors on the meet-in-the-middle key, checked against [Word.successors] (on the
   [Word] key) for every state the test visits. *)
let succ k =
  let l = ref [] in
  Back.successors k (fun t -> l := t :: !l);
  let #(a, b, c, d) = Word.successors Mitm.no_target 0 (Back.to_word k) in
  let want = List.map Back.of_word (List.filter (fun x -> x >= 0) [ a; b; c; d ]) in
  if List.sort compare !l <> List.sort compare want then fail "Back.successors of %#x" k;
  !l
;;

let preds ?(lower = -1) ?(bound = max_int) k =
  let l = ref [] in
  Back.predecessors ~lower ~bound k (fun t -> l := t :: !l);
  !l
;;

let test_inverse () =
  let first = Hashtbl.create 1024 in
  Hashtbl.replace first Back.init 0;
  let layer = ref [ Back.init ] in
  for x = 1 to depth_limit do
    let next = List.sort_uniq compare (List.concat_map succ !layer) in
    List.iter (fun k -> if not (Hashtbl.mem first k) then Hashtbl.replace first k x) next;
    layer := next
  done;
  let n = ref 0 in
  Hashtbl.iter
    (fun k x ->
      incr n;
      if Back.depth k <> x then fail "depth of %#x is %d, first reached at %d" k (Back.depth k) x;
      let w = Back.Reference.decode k in
      if Back.Reference.depth w <> x then fail "reference depth of %#x" k;
      if Back.Reference.encode w <> k then fail "decode/encode of %#x" k;
      let got = preds k in
      let sorted = List.sort compare got in
      if List.length (List.sort_uniq compare got) <> List.length got
      then fail "duplicate predecessor of %#x" k;
      let want = ref [] in
      Back.Reference.predecessors w (fun t -> want := Back.Reference.encode t :: !want);
      if sorted <> List.sort compare !want then fail "predecessors of %#x differ from the reference" k;
      (* no spurious predecessor *)
      List.iter
        (fun t -> if not (List.mem k (succ t)) then fail "spurious predecessor %#x of %#x" t k)
        got;
      (* no missing predecessor *)
      if x < depth_limit
      then
        List.iter
          (fun k2 -> if not (List.mem k (preds k2)) then fail "missing predecessor %#x of %#x" k k2)
          (succ k);
      (* the depth window filters exactly *)
      for lower = -1 to x + 1 do
        for bound = lower to x + 2 do
          let kept = List.sort compare (preds ~lower ~bound k) in
          let expect =
            List.filter
              (fun t ->
                let d = Back.depth t in
                d > lower && d <= bound)
              sorted
          in
          if kept <> expect then fail "depth window (%d, %d] of %#x" lower bound k
        done
      done)
    first;
  Printf.printf "inverse step: %d states within %d bridges\n" !n depth_limit
;;

(* Long words, beyond the [Word] key: on random balanced words of up to 54 brackets the
   packed predecessors (up to 56 brackets) equal the reference, and each leads back by a bridge
   step. *)
let test_long_words () =
  Random.init 11;
  for _ = 1 to 3000 do
    let pairs = 1 + Random.int 27 in (* predecessors add two brackets: up to 56 *)
    let w = Array.make (2 * pairs) false in
    let o = ref 0
    and c = ref 0 in
    for i = 0 to (2 * pairs) - 1 do
      let take_open = !o < pairs && (!c >= !o || Random.bool ()) in
      w.(i) <- take_open;
      if take_open then incr o else incr c
    done;
    let h = min 29 (Random.int ((2 * pairs) + 1)) in (* steps change h by one; the key holds 31 *)
    let k = Back.Reference.encode { w; h } in
    let got = List.sort compare (preds k) in
    let want = ref [] in
    Back.Reference.predecessors { w; h } (fun t ->
      if Array.length t.w <= Back.max_len then want := Back.Reference.encode t :: !want);
    if got <> List.sort compare !want then fail "long word %#x: predecessors differ" k;
    List.iter
      (fun t ->
        (* a forward step may open a pair: only words with room for two more brackets *)
        if Word.top_bit (t land Back.bits_mask) + 2 <= Back.max_len
        then (
          let l = ref [] in
          Back.successors t (fun u -> l := u :: !l);
          if not (List.mem k !l) then fail "long word %#x: %#x does not lead back" k t))
      got
  done;
  print_endline "long words: 3000 random states up to 54 brackets ok"
;;

let test_mitm (par @ local) =
  let horizon = 30 in
  let rows = Mitm.run par ~horizon ~threads:4 in
  if Array.length rows <> horizon + 1 then fail "mitm: %d rows" (Array.length rows);
  Array.iter
    (fun (r : Mitm.row) ->
      if r.count <> expected.(r.n) then fail "mitm A(%d) = %s" r.n r.count;
      match r.check with
      | Some c when c <> r.count -> fail "mitm A(%d): second split %s" r.n c
      | None when r.n > 0 -> fail "mitm A(%d): no second split" r.n
      | _ -> ())
    rows;
  (* small horizons, and a different worker count *)
  for horizon = 0 to 9 do
    Array.iter
      (fun (r : Mitm.row) ->
        if r.count <> expected.(r.n) then fail "mitm B=%d A(%d) = %s" horizon r.n r.count)
      (Mitm.run par ~horizon ~threads:3)
  done;
  print_endline "mitm: n <= 30 ok"
;;

let read path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s
;;

let test_store (par @ local) =
  let base = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "meanders-ox-store-%d" (Unix.getpid ())) in
  let a = Filename.concat base "a"
  and b = Filename.concat base "b" in
  Store.remove_all base;
  for i = 0 to 2 do
    ignore (Store.extend par ~root:a ~target:(16 + (4 * i)) ~threads:3 ~cap:2 ~out:ignore () : Store.outcome)
  done;
  ignore (Store.extend par ~root:b ~target:24 ~threads:4 ~cap:100_000 ~out:ignore () : Store.outcome);
  let va = read (Filename.concat a "values") in
  if va <> read (Filename.concat b "values") then fail "store: stepwise and direct values differ";
  let rows = List.filter (fun l -> l <> "" && l.[0] <> '#') (String.split_on_char '\n' va) in
  if List.length rows <> 25 then fail "store: %d values" (List.length rows);
  List.iter
    (fun line ->
      match String.split_on_char '\t' line with
      | [ n; c; k ] ->
        let n = int_of_string n in
        if c <> expected.(n) then fail "store A(%d) = %s" n c;
        if k <> "-" && k <> c then fail "store A(%d): second split %s" n k;
        if k = "-" && n > 0 then fail "store A(%d): no second split" n
      | _ -> fail "store: bad line %s" line)
    rows;
  Store.remove_all base;
  print_endline "store: 16 -> 20 -> 24 = 24 ok"
;;

(* Discarding backward layers gives the same values and keeps only the last layer of each side;
   pausing at a layer boundary and resuming (after a crash left a stale step behind) gives the
   same values as an uninterrupted run. *)
let test_pause_discard (par @ local) =
  let base = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "meanders-ox-pause-%d" (Unix.getpid ())) in
  let a = Filename.concat base "a"
  and b = Filename.concat base "b"
  and c = Filename.concat base "c" in
  Store.remove_all base;
  ignore (Store.extend par ~root:b ~target:22 ~threads:4 ~cap:50 ~out:ignore () : Store.outcome);
  ignore (Store.extend par ~discard:true ~root:c ~target:22 ~threads:4 ~cap:50 ~out:ignore () : Store.outcome);
  if read (Filename.concat c "values") <> read (Filename.concat b "values")
  then fail "store: discard changes the values";
  List.iter
    (fun p ->
      let n = Array.length (Sys.readdir (Filename.concat c p)) in
      if n <> 1 then fail "store: discard keeps %d layers of %s" n p)
    [ "G0"; "G1" ];
  Store.mkdir_p a;
  let pause = Filename.concat a "PAUSE" in
  let touch path = close_out (open_out_bin path) in
  let outcome =
    Store.extend par ~root:a ~target:22 ~threads:4 ~cap:50 ~out:(fun line ->
      if String.length line >= 6 && String.sub line 0 6 = "G1   5" then touch pause) ()
  in
  if outcome <> Store.Paused then fail "store: no pause";
  let g6 = Filename.concat (Filename.concat a "G1") "006" in
  let tmp = Filename.concat g6 "tmp" in
  Store.mkdir_p tmp;
  let oc = open_out_bin (Filename.concat tmp "spill") in
  output_string oc "\001\002\003";
  close_out oc;
  let oc = open_out_bin (Filename.concat g6 "seg0.dat") in
  output_string oc "garbage";
  close_out oc;
  Sys.remove pause;
  if Store.extend par ~root:a ~target:22 ~threads:4 ~cap:50 ~out:ignore () <> Store.Complete
  then fail "store: no resume";
  if Sys.file_exists tmp then fail "store: stale spill kept";
  if read (Filename.concat a "values") <> read (Filename.concat b "values")
  then fail "store: pause and resume change the values";
  Store.remove_all base;
  print_endline "store: discard and pause/resume ok"
;;

let () =
  (* the exact two-limb arithmetic *)
  let #(h, l) = Limb.mul 0 Limb.mask 0 Limb.mask in
  if Limb.to_string h l <> "21267647932558653957237540927630737409"
  then fail "Limb.mul (2^62-1)^2 = %s" (Limb.to_string h l);
  let #(h, l) = Limb.add 0 Limb.mask 0 1 in
  if Limb.to_string h l <> "4611686018427387904" then fail "Limb.add carry";
  (* the store's radix sort of a table *)
  Random.init 7;
  List.iter
    (fun n ->
      let t = Mitm.Table.create 64 in
      let keys = Hashtbl.create 16 in
      for _ = 1 to n do
        (* all 63 bits: keys with h >= 16 are negative ints, ordered unsigned *)
        let k = Random.bits () lor (Random.bits () lsl 30) lor (Random.bits () lsl 60) in
        Hashtbl.replace keys k ();
        Mitm.Table.add t k 0 1
      done;
      let c, m = Store.sorted t in
      let want =
        List.sort
          (fun a b -> compare (Store.bias a) (Store.bias b))
          (Hashtbl.fold (fun k () a -> k :: a) keys [])
      in
      if List.init m (fun i -> Sweep.uget c (3 * i) - 1) <> want then fail "Store.sorted, n = %d" n)
    [ 0; 1; 2; 17; 1000; 20000 ];
  test_inverse ();
  test_long_words ();
  Parallel_scheduler.with_parallel ~max_workers:4 (fun par ->
    test_mitm par;
    test_store par;
    test_pause_discard par [@nontail]);
  print_endline "ok"
;;
