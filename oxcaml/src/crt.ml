(* Recovering the exact count from its residues modulo 2^63 and modulo p = 2^61 - 1, and
   printing the ~124-bit result in decimal, with no bignum library.

   An OCaml [int] is 63 bits, so the residue [a] modulo 2^63 is held in an [int] whose bit
   pattern is the unsigned value: [a_u = (a land max_int) + 2^62 * (1 if a < 0)].
   The answer is x = a_u + 2^63 t with t = (b - a_u) * 2^-63 mod p. Since 2^61 = 1 (mod p),
   2^63 = 4 and 4^-1 = 2^59 (mod p); multiplying a residue by 2^59 is a 61-bit rotation.
   x < 2^63 p < 2^124. *)

let p = (1 lsl 61) - 1

(* [a_u mod p]: a_u = lo + 2^62 hi and 2^62 = 2 (mod p). *)
let unsigned_mod_p a =
  let lo = a land max_int
  and hi = if a < 0 then 1 else 0 in
  ((lo mod p) + (2 * hi)) mod p
;;

(* [x * 2^59 mod p] for 0 <= x < p: x = 4q + r, x 2^59 = q 2^61 + r 2^59 = q + r 2^59. *)
let times_2_59 x = (x lsr 2) lor ((x land 3) lsl 59)

let t_of a b = times_2_59 ((b - unsigned_mod_p a + p) mod p)

(* Decimal digits of a_u + 2^63 t, using base-10^9 limbs (little-endian) in an int array. *)
let base = 1_000_000_000

let to_limbs v =
  (* v >= 0 *)
  let rec go v acc = if v = 0 then List.rev acc else go (v / base) ((v mod base) :: acc) in
  Array.of_list (go v [])
;;

let mul_small limbs k =
  (* limbs * k, k <= 2^21 so each partial product < 2^51 *)
  let carry = ref 0 in
  let out =
    Array.map
      (fun d ->
        let v = (d * k) + !carry in
        carry := v / base;
        v mod base)
      limbs
  in
  Array.append out (to_limbs !carry)
;;

let add_limbs a b =
  let n = max (Array.length a) (Array.length b) in
  let get x i = if i < Array.length x then x.(i) else 0 in
  let carry = ref 0 in
  let out =
    Array.init n (fun i ->
      let v = get a i + get b i + !carry in
      carry := v / base;
      v mod base)
  in
  Array.append out (to_limbs !carry)
;;

let to_string limbs =
  let n = ref (Array.length limbs) in
  while !n > 1 && limbs.(!n - 1) = 0 do
    decr n
  done;
  if !n = 0
  then "0"
  else (
    let buf = Buffer.create 64 in
    Buffer.add_string buf (string_of_int limbs.(!n - 1));
    for i = !n - 2 downto 0 do
      Buffer.add_string buf (Printf.sprintf "%09d" limbs.(i))
    done;
    Buffer.contents buf)
;;

(* The limbs of the unsigned 63-bit value held in [a]. *)
let unsigned_limbs a =
  let lo = a land max_int in
  if a < 0 then add_limbs (to_limbs lo) (mul_small (to_limbs (1 lsl 31)) (1 lsl 31)) else to_limbs lo
;;

(* The decimal value of the [x] with x = a (mod 2^63), x = b (mod 2^61 - 1), 0 <= x < 2^63 p. *)
let combine a b =
  let t = t_of a b in
  let hi = mul_small (mul_small (mul_small (to_limbs t) (1 lsl 21)) (1 lsl 21)) (1 lsl 21) in
  to_string (add_limbs (unsigned_limbs a) hi)
;;

(* The decimal value of a residue modulo 2^63 read as unsigned (exact when x < 2^63). *)
let unsigned_to_string a = to_string (unsigned_limbs a)
