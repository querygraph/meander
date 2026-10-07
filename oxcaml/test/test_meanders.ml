(* Unit tests: the CRT recombination on values >= 2^63 (which the CLI only reaches for
   n >= 44), and the parallel sweep against the serial one and the known counts. *)

let crt_cases =
  [ -170565359224969352, 2135277649988724607, "18276178714484582264" (* A005316(44) *)
  ; 874752366329603288, 874752366329603320, "74661728661167809752" (* A005316(45) *)
  ; 218680114456339724, 218680114456339808, "193909492888406631692" (* A005316(46) *)
  ; 0, 4, "9223372036854775808"
  ; -1, 3, "9223372036854775807"
  ; 1, 5, "9223372036854775809"
  ; -1, 2305843009213693950, "21267647932558653957237540927630737407" (* max *)
  ; -2162430062396714416, 143412946816979539, "7060941974458061392" (* A005316(43) *)
  ; 0, 0, "0"
  ; 1, 1, "1"
  ]
;;

let expected =
  [| "1"; "1"; "1"; "2"; "3"; "8"; "14"; "42"; "81"; "262"; "538"; "1828"; "3926"; "13820"
   ; "30694"; "110954"; "252939"; "933458"; "2172830"; "8152860"; "19304190"; "73424650"
   ; "176343390"; "678390116"; "1649008456"; "6405031050"; "15730575554"; "61606881612"
   ; "152663683494"
  |]
;;

let () =
  List.iter
    (fun (a, b, want) ->
      let got = Meanders.Crt.combine a b in
      if got <> want then failwith (Printf.sprintf "Crt.combine: got %s, want %s" got want))
    crt_cases;
  Parallel_scheduler.with_parallel ~max_workers:4 (fun par ->
    for m = 0 to Array.length expected - 1 do
        let want = expected.(m) in
        let serial = Meanders.Crt.unsigned_to_string (Meanders.Serial.count m) in
        let par1 = Meanders.count par ~m ~threads:4 ~two_moduli:false in
        let par2 = Meanders.count par ~m ~threads:3 ~two_moduli:true in
        if serial <> want || par1.count <> want || par2.count <> want
        then
          failwith
            (Printf.sprintf
               "n=%d: want %s, serial %s, parallel %s, two moduli %s"
               m
               want
               serial
               par1.count
               par2.count)
    done);
  print_endline "ok"
;;
