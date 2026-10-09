module Word = Word
module Serial = Serial
module Sweep = Sweep
module Crt = Crt
module Back = Back
module Limb = Limb
module Mitm = Mitm
module Store = Store

type stats =
  { count : string
  ; peak_states : int
  ; total_states : int
  }

(* Count the meanders with [m] crossings. A second sweep modulo 2^61 - 1 runs when the count
   might reach 2^63 (m >= 44; A005316(43) < 2^63 <= A005316(44)), or when forced. *)
let count (par @ local) ~m ~threads ~two_moduli =
  let a, peak, total = Sweep.Run63.sweep par ~m ~threads in
  let count =
    if m >= 44 || two_moduli
    then (
      let b, _, _ = Sweep.Run61.sweep par ~m ~threads in
      Crt.combine a b)
    else Crt.unsigned_to_string a
  in
  { count; peak_states = peak; total_states = total }
;;
