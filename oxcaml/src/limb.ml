(* Exact counts as two 62-bit limbs: the value [hi * 2^62 + lo] with [0 <= lo < 2^62] and
   [0 <= hi < 2^62], so up to 2^124 (Rust uses [u128]). Every function returns unboxed pairs
   [#(hi, lo)] in registers.

   Adding two limbs [lo1 + lo2 < 2^63] overflows a signed 63-bit [int] but not its bit
   pattern: the carry is bit 62, read with a logical shift. *)

let bits = 62
let mask = (1 lsl bits) - 1
let m31 = (1 lsl 31) - 1

let[@inline always] add ah al bh bl =
  let s = al + bl in
  #(ah + bh + (s lsr bits), s land mask)
;;

(* The exact 124-bit product of two 62-bit limbs, as 31-bit halves:
   a b = a1 b1 2^62 + (a1 b0 + a0 b1) 2^31 + a0 b0, each partial product < 2^62. *)
let mul62 a b =
  let a0 = a land m31
  and a1 = a lsr 31
  and b0 = b land m31
  and b1 = b lsr 31 in
  let m1 = a1 * b0
  and m2 = a0 * b1 in
  let s = (a0 * b0) + ((m1 land m31) lsl 31) in
  let c1 = s lsr bits in
  let s = (s land mask) + ((m2 land m31) lsl 31) in
  let c2 = s lsr bits in
  #((a1 * b1) + (m1 lsr 31) + (m2 lsr 31) + c1 + c2, s land mask)
;;

let overflow () = failwith "Limb: count exceeds 2^124"

(* [a * b] for two-limb values whose product is below 2^124 (checked). *)
let[@inline never] mul_slow ah al bh bl =
  if ah <> 0 && bh <> 0 then overflow ();
  let #(ph, pl) = mul62 al bl in
  let cross a b = if a <> 0 && b > (mask / a) then overflow () else a * b in
  let h = ph + cross ah bl + cross bh al in
  if h < 0 || h > mask then overflow ();
  #(h, pl)
;;

let[@inline always] mul ah al bh bl =
  if ah lor bh = 0 && al lor bl <= m31 then #(0, al * bl) else mul_slow ah al bh bl
;;

(* Decimal, with the base-10^9 limb routines of [Crt]. *)
let to_string hi lo =
  if hi < 0 || hi > mask then overflow ();
  let open Crt in
  let h = mul_small (mul_small (mul_small (to_limbs hi) (1 lsl 21)) (1 lsl 21)) (1 lsl 20) in
  Crt.to_string (add_limbs (to_limbs lo) h)
;;
