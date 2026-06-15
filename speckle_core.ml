
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val pred : int -> int **)

let pred = fun n -> Stdlib.max 0 (n-1)

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (add_carry p q0))
        (fun q0 -> (fun p->2*p) (add_carry p q0))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->2*p) (add_carry p q0))
        (fun q0 -> (fun p->1+2*p) (add p q0))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (succ q0))
        (fun q0 -> (fun p->2*p) (succ q0))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun q0 -> succ_double_mask (sub_mask p q0))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double_mask (sub_mask_carry p q0))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Stdlib.max 1 (n-m)

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val pow : int -> int -> int **)

  let pow x =
    iter (mul x) 1

  (** val size_nat : int -> int **)

  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun _ -> Stdlib.Int.succ 0)
      p

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb p q0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        (fun _ -> false)
        q0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        q0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q0)
      p

  (** val ggcdn : int -> int -> int -> int * (int * int) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (1, (a, b)))
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (1, 1))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in (g, (aa, (add aa ((fun p->2*p) ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in (g, ((add bb ((fun p->2*p) ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, ((fun p->2*p) bb))))
          (fun _ -> (1, (a, 1)))
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ ->
          let (g, p) = ggcdn n0 a0 b in
          let (aa, bb) = p in (g, (((fun p->2*p) aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a0 b0 in (((fun p->2*p) g), p))
          (fun _ -> (1, (a, 1)))
          b)
        (fun _ -> (1, (1, b)))
        a)
      n

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val of_nat : int -> int **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 1)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Coq_Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Coq_Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double (pos_sub p q0))
        (fun q0 -> succ_double (pos_sub p q0))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> pred_double (pos_sub p q0))
        (fun q0 -> double (pos_sub p q0))
        (fun _ -> (Coq_Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (~-) ((fun p->2*p) q0))
        (fun q0 -> (~-) (Coq_Pos.pred_double q0))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val pred : int -> int **)

  let pred = Stdlib.Int.pred

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val sgn : int -> int **)

  let sgn z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun _ -> 1)
      (fun _ -> (~-) 1)
      z0

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q0 -> Coq_Pos.eqb p q0)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q0 -> Coq_Pos.eqb p q0)
        y)
      x

  (** val max : int -> int -> int **)

  let max = Stdlib.max

  (** val min : int -> int -> int **)

  let min = Stdlib.min

  (** val abs : int -> int **)

  let abs = Stdlib.Int.abs

  (** val to_nat : int -> int **)

  let to_nat z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> Coq_Pos.to_nat p)
      (fun _ -> 0)
      z0

  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n0 -> (Coq_Pos.of_succ_nat n0))
      n

  (** val to_pos : int -> int **)

  let to_pos z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> p)
      (fun _ -> 1)
      z0

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = add (mul ((fun p->2*p) 1) r) 1 in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q0), r')
      else ((add (mul ((fun p->2*p) 1) q0) 1), (sub r' b)))
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul ((fun p->2*p) 1) r in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q0), r')
      else ((add (mul ((fun p->2*p) 1) q0) 1), (sub r' b)))
      (fun _ -> if leb ((fun p->2*p) 1) b then (0, 1) else (1, 0))
      a

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun _ -> pos_div_eucl a' b)
        (fun b' ->
        let (q0, r) = pos_div_eucl a' b' in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q0), 0))
           (fun _ -> ((opp (add q0 1)), (add b r)))
           (fun _ -> ((opp (add q0 1)), (add b r)))
           r))
        b)
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun _ ->
        let (q0, r) = pos_div_eucl a' b in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q0), 0))
           (fun _ -> ((opp (add q0 1)), (sub b r)))
           (fun _ -> ((opp (add q0 1)), (sub b r)))
           r))
        (fun b' -> let (q0, r) = pos_div_eucl a' b' in (q0, (opp r)))
        b)
      a

  (** val div : int -> int -> int **)

  let div = (fun a b -> if b = 0 then 0 else
     let q = a / b and r = a mod b in
     if r <> 0 && (r < 0) <> (b < 0) then q - 1 else q)

  (** val modulo : int -> int -> int **)

  let modulo = (fun a b -> if b = 0 then a else
     let r = a mod b in
     if r <> 0 && (r < 0) <> (b < 0) then r + b else r)

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> ((abs b), (0, (sgn b))))
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> ((abs a), ((sgn a), 0)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in (g, (aa, bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (aa, ((~-) bb))))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> ((abs a), ((sgn a), 0)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (((~-) aa), bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (((~-) aa), ((~-) bb))))
        b)
      a
 end

(** val z_lt_dec : int -> int -> bool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val z_lt_ge_dec : int -> int -> bool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_lt_le_dec : int -> int -> bool **)

let z_lt_le_dec =
  z_lt_ge_dec

(** val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

let rec pow_pos rmul x i =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun i0 -> let p = pow_pos rmul x i0 in rmul x (rmul p p))
    (fun i0 -> let p = pow_pos rmul x i0 in rmul p p)
    (fun _ -> x)
    i

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> default
              | x :: _ -> x)
    (fun m -> match l with
              | [] -> default
              | _ :: t -> nth m t default)
    n

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: t -> app (f x) (flat_map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Stdlib.Int.succ start) len0))
    len

type q = { qnum : int; qden : int }

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum y.qden) (Z.mul y.qnum x.qden)); qden =
    (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> { qnum = 0; qden = 1 })
    (fun p -> { qnum = x.qden; qden = p })
    (fun p -> { qnum = ((~-) x.qden); qden = p })
    x.qnum

(** val qlt_le_dec : q -> q -> bool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul x.qnum y.qden) (Z.mul y.qnum x.qden)

(** val qarchimedean : q -> int **)

let qarchimedean q0 =
  let { qnum = qnum0; qden = _ } = q0 in
  ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
     (fun _ -> 1)
     (fun p -> Coq_Pos.add p 1)
     (fun _ -> 1)
     qnum0)

(** val qpower_positive : q -> int -> q **)

let qpower_positive =
  pow_pos qmult

(** val qpower : q -> int -> q **)

let qpower q0 z0 =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> { qnum = 1; qden = 1 })
    (fun p -> qpower_positive q0 p)
    (fun p -> qinv (qpower_positive q0 p))
    z0

(** val qabs : q -> q **)

let qabs x =
  let { qnum = n; qden = d } = x in { qnum = (Z.abs n); qden = d }

(** val pos_log2floor_plus1 : int -> int **)

let rec pos_log2floor_plus1 p =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun p' -> Coq_Pos.succ (pos_log2floor_plus1 p'))
    (fun p' -> Coq_Pos.succ (pos_log2floor_plus1 p'))
    (fun _ -> 1)
    p

(** val qbound_lt_ZExp2 : q -> int **)

let qbound_lt_ZExp2 q0 =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> (~-) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1))))))))))
    (fun p ->
    Z.pos_sub (Coq_Pos.succ (pos_log2floor_plus1 p))
      (pos_log2floor_plus1 q0.qden))
    (fun _ -> 0)
    q0.qnum

type cReal = { seq0 : (int -> q); scale : int }

(** val sig_forall_dec : (int -> bool) -> int option **)

let sig_forall_dec = (fun _ -> None)

(** val lowerCutBelow : (q -> bool) -> q **)

let lowerCutBelow f =
  let s =
    sig_forall_dec (fun n ->
      let b = f (qopp { qnum = (Z.of_nat n); qden = 1 }) in
      if b then false else true)
  in
  (match s with
   | Some s0 -> qopp { qnum = (Z.of_nat s0); qden = 1 }
   | None -> assert false (* absurd case *))

(** val lowerCutAbove : (q -> bool) -> q **)

let lowerCutAbove f =
  let s =
    sig_forall_dec (fun n ->
      let b = f { qnum = (Z.of_nat n); qden = 1 } in if b then true else false)
  in
  (match s with
   | Some s0 -> { qnum = (Z.of_nat s0); qden = 1 }
   | None -> assert false (* absurd case *))

type dReal = (q -> bool)

(** val dRealQlim_rec : (q -> bool) -> int -> int -> q **)

let rec dRealQlim_rec f n p =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> assert false (* absurd case *))
    (fun n0 ->
    let b =
      f
        (qplus (lowerCutBelow f) { qnum = (Z.of_nat n0); qden =
          (Coq_Pos.of_nat (Stdlib.Int.succ n)) })
    in
    if b
    then qplus (lowerCutBelow f) { qnum = (Z.of_nat n0); qden =
           (Coq_Pos.of_nat (Stdlib.Int.succ n)) }
    else dRealQlim_rec f n n0)
    p

(** val dRealAbstr : cReal -> dReal **)

let dRealAbstr x =
  let h = fun q0 n ->
    let s =
      qlt_le_dec
        (qplus q0
          (qpower { qnum = ((fun p->2*p) 1); qden = 1 } (Z.opp (Z.of_nat n))))
        (x.seq0 (Z.opp (Z.of_nat n)))
    in
    if s then false else true
  in
  (fun q0 -> match sig_forall_dec (h q0) with
             | Some _ -> true
             | None -> false)

(** val dRealQlim : dReal -> int -> q **)

let dRealQlim x n =
  let s = lowerCutAbove x in
  let s0 = qarchimedean (qminus s (lowerCutBelow x)) in
  dRealQlim_rec x n (mul (Stdlib.Int.succ n) (Coq_Pos.to_nat s0))

(** val dRealQlimExp2 : dReal -> int -> q **)

let dRealQlimExp2 x n =
  dRealQlim x (pred (Nat.pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) n))

(** val cReal_of_DReal_seq : dReal -> int -> q **)

let cReal_of_DReal_seq x n =
  dRealQlimExp2 x (Z.to_nat (Z.opp n))

(** val cReal_of_DReal_scale : dReal -> int **)

let cReal_of_DReal_scale x =
  qbound_lt_ZExp2
    (qplus (qabs (cReal_of_DReal_seq x ((~-) 1))) { qnum = ((fun p->2*p) 1);
      qden = 1 })

(** val dRealRepr : dReal -> cReal **)

let dRealRepr x =
  { seq0 = (cReal_of_DReal_seq x); scale = (cReal_of_DReal_scale x) }

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl =
 struct
  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst =
    dRealAbstr

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr =
    dRealRepr

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

module type RinvSig =
 sig
  val coq_Rinv : float -> float
 end

module RinvImpl =
 struct
  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end

(** val q2R : q -> float **)

let q2R x =
  ( *. ) (float_of_int x.qnum) ((fun x -> 1.0 /. x) (float_of_int x.qden))

type gimage = { gw : int; gh : int; gpix : (int -> int -> int) }

(** val gw : gimage -> int **)

let gw g =
  g.gw

(** val gh : gimage -> int **)

let gh g =
  g.gh

(** val zw : gimage -> int **)

let zw img =
  Z.of_nat img.gw

(** val zh : gimage -> int **)

let zh img =
  Z.of_nat img.gh

(** val inb : gimage -> int -> int -> bool **)

let inb img x y =
  (&&) ((&&) ((&&) (Z.leb 0 x) (Z.ltb x (zw img))) (Z.leb 0 y))
    (Z.ltb y (zh img))

(** val oob0 : gimage -> int -> int -> int **)

let oob0 img x y =
  if inb img x y then img.gpix x y else 0

(** val wrapidx : int -> int -> int **)

let wrapidx i n =
  if (=) n 0 then 0 else Z.modulo i (Z.of_nat n)

(** val wrap : gimage -> int -> int -> int **)

let wrap img x y =
  img.gpix (wrapidx x img.gw) (wrapidx y img.gh)

(** val gfrom_list : int -> int -> int list -> gimage **)

let gfrom_list w h d =
  { gw = w; gh = h; gpix = (fun x y ->
    if (&&) ((&&) ((&&) (Z.leb 0 x) (Z.ltb x (Z.of_nat w))) (Z.leb 0 y))
         (Z.ltb y (Z.of_nat h))
    then nth (Z.to_nat (Z.add (Z.mul y (Z.of_nat w)) x)) d 0
    else 0) }

(** val c_cardinal : (int * int) list **)

let c_cardinal =
  (0, 1) :: ((1, 0) :: ((0, ((~-) 1)) :: ((((~-) 1), 0) :: [])))

(** val c_all : (int * int) list **)

let c_all =
  (0, 1) :: ((1, 1) :: ((1, 0) :: ((1, ((~-) 1)) :: ((0, ((~-) 1)) :: ((((~-)
    1), ((~-) 1)) :: ((((~-) 1), 0) :: ((((~-) 1), 1) :: [])))))))

(** val c_offsets : bool -> (int * int) list **)

let c_offsets = function
| true -> c_all
| false -> c_cardinal

type coord = int * int

(** val coord_eqb : coord -> coord -> bool **)

let coord_eqb a b =
  (&&) (Z.eqb (fst a) (fst b)) (Z.eqb (snd a) (snd b))

(** val cmem : coord -> coord list -> bool **)

let cmem c l =
  existsb (coord_eqb c) l

(** val zrange : int -> int list **)

let zrange k =
  map Z.of_nat (seq 0 k)

(** val gcoords : gimage -> coord list **)

let gcoords img =
  flat_map (fun x -> map (fun y -> (x, y)) (zrange img.gh)) (zrange img.gw)

(** val inbox : int -> int -> int -> int -> int -> int -> bool **)

let inbox xmin xmax ymin ymax x y =
  (&&) ((&&) ((&&) (Z.leb xmin x) (Z.leb x xmax)) (Z.leb ymin y))
    (Z.leb y ymax)

(** val zround_div : int -> int -> int **)

let zround_div a b =
  if (=) b 0
  then 0
  else Z.div (Z.add (Z.mul ((fun p->2*p) 1) a) (Z.of_nat b))
         (Z.mul ((fun p->2*p) 1) (Z.of_nat b))

(** val scan :
    gimage -> coord list -> int -> int -> ((int * int) * int) * int **)

let scan img offs x y =
  fold_left (fun st o ->
    let (y0, ec) = st in
    let (y1, my) = y0 in
    let (mint, mx) = y1 in
    let xt = Z.add x (fst o) in
    let yt = Z.add y (snd o) in
    let ib = inb img xt yt in
    let val0 = oob0 img xt yt in
    let replace = (<) mint val0 in
    let equal = (&&) ((=) val0 mint) ib in
    let ec' =
      if replace then 0 else add ec (if equal then Stdlib.Int.succ 0 else 0)
    in
    let mint' = if replace then val0 else mint in
    let mx' = if replace then xt else mx in
    let my' = if replace then yt else my in (((mint', mx'), my'), ec')) offs
    ((((oob0 img x y), x), y), 0)

type sres =
| RSolved of coord
| RPlateau
| RAscend of coord

(** val classify : gimage -> coord list -> int -> int -> sres **)

let classify img offs x y =
  let (p, ec) = scan img offs x y in
  let (p0, my) = p in
  let (mint, mx) = p0 in
  if (=) mint (oob0 img x y)
  then if (=) ec 0 then RSolved (x, y) else RPlateau
  else RAscend (mx, my)

(** val floodfuel : gimage -> coord list -> int **)

let floodfuel img offs =
  Stdlib.Int.succ (mul (mul img.gw img.gh) (Stdlib.Int.succ (length offs)))

(** val same_int : gimage -> int -> coord -> bool **)

let same_int img ri q0 =
  (&&) (inb img (fst q0) (snd q0)) ((=) (oob0 img (fst q0) (snd q0)) ri)

(** val rflood :
    gimage -> coord list -> int -> int -> coord list -> coord list -> coord
    list **)

let rec rflood img offs ri fuel stack visited =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> visited)
    (fun f ->
    match stack with
    | [] -> visited
    | p :: rest ->
      if cmem p visited
      then rflood img offs ri f rest visited
      else let nbrs =
             map (fun o -> ((Z.add (fst p) (fst o)),
               (Z.add (snd p) (snd o)))) offs
           in
           let good =
             filter (fun q0 ->
               (&&) (same_int img ri q0) (negb (cmem q0 visited))) nbrs
           in
           rflood img offs ri f (app good rest) (p :: visited))
    fuel

(** val region : gimage -> coord list -> coord -> coord list **)

let region img offs s =
  rflood img offs (oob0 img (fst s) (snd s)) (floodfuel img offs) (s :: []) []

(** val pixel_ascends : gimage -> coord list -> int -> coord -> bool **)

let pixel_ascends img offs ri p =
  existsb (fun o ->
    let qx = Z.add (fst p) (fst o) in
    let qy = Z.add (snd p) (snd o) in
    (&&) (inb img qx qy) ((<) ri (oob0 img qx qy))) offs

(** val region_ascends : gimage -> coord list -> int -> coord list -> bool **)

let region_ascends img offs ri r =
  existsb (pixel_ascends img offs ri) r

(** val region_centroid : coord list -> coord **)

let region_centroid r =
  let cnt = length r in
  let sx = fold_right (fun q0 a -> Z.add (fst q0) a) 0 r in
  let sy = fold_right (fun q0 a -> Z.add (snd q0) a) 0 r in
  ((zround_div sx cnt), (zround_div sy cnt))

(** val solve : gimage -> coord list -> int -> coord -> coord option **)

let rec solve img offs fuel p =
  match classify img offs (fst p) (snd p) with
  | RSolved q0 -> Some q0
  | RPlateau ->
    let ri = oob0 img (fst p) (snd p) in
    let r = region img offs p in
    if region_ascends img offs ri r then None else Some (region_centroid r)
  | RAscend q0 ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> None)
       (fun f -> solve img offs f q0)
       fuel)

(** val fuel0 : gimage -> int **)

let fuel0 img =
  Stdlib.Int.succ (mul img.gw img.gh)

(** val solveP : gimage -> coord list -> coord -> coord option **)

let solveP img offs p =
  solve img offs (fuel0 img) p

(** val weight : gimage -> coord list -> coord -> int **)

let weight img offs c =
  length
    (filter (fun p ->
      match solveP img offs p with
      | Some q0 -> coord_eqb q0 c
      | None -> false) (gcoords img))

(** val candidates : gimage -> coord list -> coord list **)

let candidates img offs =
  fold_left (fun acc p ->
    match solveP img offs p with
    | Some q0 -> if cmem q0 acc then acc else app acc (q0 :: [])
    | None -> acc) (gcoords img) []

(** val peaks_default :
    gimage -> int -> coord list -> int -> int -> int -> int ->
    ((int * int) * int) list **)

let peaks_default img t offs xmin xmax ymin ymax =
  fold_right (fun c acc ->
    let (cx, cy) = c in
    if (&&) (inbox xmin xmax ymin ymax cx cy) ((<) t (weight img offs c))
    then ((cx, cy), (weight img offs c)) :: acc
    else acc) [] (candidates img offs)

(** val peaks :
    gimage -> int -> bool -> int -> int -> int -> int -> ((int * int) * int)
    list **)

let peaks img t all_adjacent xmin xmax ymin ymax =
  peaks_default img t (c_offsets all_adjacent) xmin xmax ymin ymax

(** val peaks_full : gimage -> int -> bool -> ((int * int) * int) list **)

let peaks_full img t all_adjacent =
  peaks img t all_adjacent 0 (Z.sub (zw img) 1) 0 (Z.sub (zh img) 1)

(** val gxmin : gimage -> float **)

let gxmin _ =
  float_of_int 1

(** val gymin : gimage -> float **)

let gymin _ =
  float_of_int 1

(** val gxmax : gimage -> float **)

let gxmax img =
  float_of_int (Z.sub (zw img) ((fun p->2*p) 1))

(** val gymax : gimage -> float **)

let gymax img =
  float_of_int (Z.sub (zh img) ((fun p->2*p) 1))

(** val arange_aux : int -> float -> float -> float -> float list **)

let rec arange_aux fuel cur stop step =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun f ->
    if (fun x y -> x < y) cur stop
    then cur :: (arange_aux f ((+.) cur step) stop step)
    else [])
    fuel

(** val arange_count : float -> float -> float -> int **)

let arange_count start stop step =
  if (fun x y -> x <= y) step (float_of_int 0)
  then 0
  else add
         (Z.to_nat
           ((fun x -> (int_of_float (floor x)) + 1)
             ((/.) ((-.) stop start) step))) (Stdlib.Int.succ
         (Stdlib.Int.succ 0))

(** val arange : float -> float -> float -> float list **)

let arange start stop step =
  arange_aux (arange_count start stop step) start stop step

(** val radius_of_area : float -> float **)

let radius_of_area pixel_area =
  Stdlib.sqrt ((/.) pixel_area (4.0 *. atan 1.0))

(** val square_spacing : float -> float -> float **)

let square_spacing radius density =
  (-.)
    (( *. )
      (q2R { qnum = ((fun p->1+2*p) ((fun p->2*p) 1)); qden = ((fun p->2*p)
        ((fun p->1+2*p) ((fun p->2*p) 1))) })
      (Stdlib.sqrt
        ((/.)
          (( *. )
            (( *. )
              (float_of_int ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))
              (4.0 *. atan 1.0)) (( *. ) radius radius)) density)))
    (( *. ) (float_of_int ((fun p->1+2*p) 1)) radius)

(** val square_grid : gimage -> float -> float -> (float * float) list **)

let square_grid img radius density =
  let sp = square_spacing radius density in
  let xs =
    arange ((+.) ((+.) sp radius) (gxmin img))
      ((-.) ((-.) (gxmax img) radius) sp)
      (( *. ) (float_of_int ((fun p->2*p) 1)) ((+.) sp radius))
  in
  let ys =
    arange ((+.) ((+.) sp radius) (gymin img))
      ((-.) ((-.) (gymax img) radius) sp)
      (( *. ) (float_of_int ((fun p->2*p) 1)) ((+.) sp radius))
  in
  flat_map (fun y -> map (fun x -> (x, y)) xs) ys

(** val hex_hspacing : float -> float -> float **)

let hex_hspacing radius density =
  ( *. )
    (( *. )
      ((/.) (float_of_int ((fun p->2*p) 1))
        (float_of_int ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))
      ((-.)
        ((/.)
          (( *. )
            ((fun x y -> exp (y *. log x)) (float_of_int ((fun p->1+2*p) 1))
              ((/.) (float_of_int 1)
                (float_of_int ((fun p->2*p) ((fun p->2*p) 1)))))
            (Stdlib.sqrt
              (( *. )
                (float_of_int ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
                  1)))) (4.0 *. atan 1.0)))) (Stdlib.sqrt density))
        (float_of_int ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
    radius

(** val hex_vspacing : float -> float -> float **)

let hex_vspacing radius hspacing =
  ( *. ) (Stdlib.sqrt (float_of_int ((fun p->1+2*p) 1)))
    ((+.) radius ((/.) hspacing (float_of_int ((fun p->2*p) 1))))

(** val hex_rows :
    int -> float list -> float list -> float -> float -> (float * float) list **)

let rec hex_rows idx ys xs r hs =
  match ys with
  | [] -> []
  | y :: ys' ->
    let row =
      map (fun x ->
        if (fun n -> n mod 2 = 0) idx
        then (x, y)
        else (((+.) ((+.) x r) hs), y)) xs
    in
    app row (hex_rows (Stdlib.Int.succ idx) ys' xs r hs)

(** val hex_grid : gimage -> float -> float -> (float * float) list **)

let hex_grid img radius density =
  let hs = hex_hspacing radius density in
  let vs = hex_vspacing radius hs in
  let xs =
    arange
      ((+.) ((+.) hs (( *. ) (float_of_int ((fun p->2*p) 1)) radius))
        (gxmin img))
      ((-.) (gxmax img)
        (( *. ) (float_of_int ((fun p->2*p) 1))
          ((+.) (( *. ) (float_of_int ((fun p->2*p) 1)) radius) hs)))
      (( *. ) (float_of_int ((fun p->2*p) 1)) ((+.) hs radius))
  in
  let ys =
    arange
      ((+.) ((+.) radius (gymin img))
        ((/.) vs (float_of_int ((fun p->2*p) 1))))
      ((-.) ((-.) (gymax img) radius)
        ((/.) vs (float_of_int ((fun p->2*p) 1)))) vs
  in
  hex_rows 0 ys xs radius hs

type grid_style =
| GSquare
| GHex

(** val element_grid :
    grid_style -> gimage -> float -> float -> (float * float) list **)

let element_grid style img radius density =
  match style with
  | GSquare -> square_grid img radius density
  | GHex -> hex_grid img radius density

(** val floorZ : float -> int **)

let floorZ =
  (fun x -> int_of_float (floor x))

(** val ceilZ : float -> int **)

let ceilZ x =
  Z.opp ((fun x -> int_of_float (floor x)) ((~-.) x))

(** val zseq_incl : int -> int -> int list **)

let zseq_incl lo hi =
  map (fun i -> Z.add lo (Z.of_nat i))
    (seq 0 (Z.to_nat (Z.add (Z.sub hi lo) 1)))

(** val subpix_off : int -> int -> int -> float **)

let subpix_off a b point =
  if (=) a b
  then float_of_int 0
  else if (<) b a
       then (~-.)
              ((/.) (float_of_int a)
                (( *. ) (float_of_int ((fun p->2*p) 1)) (float_of_int point)))
       else (/.) (float_of_int b)
              (( *. ) (float_of_int ((fun p->2*p) 1)) (float_of_int point))

(** val grid_element_encoding :
    gimage -> gimage -> float -> float -> float -> bool **)

let grid_element_encoding peakmap orig cx cy radius =
  let x_min = floorZ ((-.) cx radius) in
  let x_max = ceilZ ((+.) cx radius) in
  let y_min = floorZ ((-.) cy radius) in
  let y_max = ceilZ ((+.) cy radius) in
  existsb (fun xy ->
    let (x_tmp, y_tmp) = xy in
    let point = wrap orig x_tmp y_tmp in
    let left = wrap orig (Z.sub x_tmp 1) y_tmp in
    let right = wrap orig (Z.add x_tmp 1) y_tmp in
    let up = wrap orig x_tmp (Z.sub y_tmp 1) in
    let down = wrap orig x_tmp (Z.add y_tmp 1) in
    if (&&) ((<) 0 (wrap peakmap x_tmp y_tmp)) ((<) 0 point)
    then let x_off = subpix_off left right point in
         let y_off = subpix_off up down point in
         let dx = (-.) ((+.) (float_of_int x_tmp) x_off) cx in
         let dy = (-.) ((+.) (float_of_int y_tmp) y_off) cy in
         let dist = Stdlib.sqrt ((+.) (( *. ) dx dx) (( *. ) dy dy)) in
         if (fun x y -> x <= y) dist radius then true else false
    else false)
    (flat_map (fun y -> map (fun x -> (x, y)) (zseq_incl x_min x_max))
      (zseq_incl y_min y_max))

(** val grid_encode :
    grid_style -> gimage -> gimage -> float -> float -> bool list **)

let grid_encode style peakmap orig pixel_area density =
  let radius = radius_of_area pixel_area in
  map (fun c ->
    let (cx, cy) = c in grid_element_encoding peakmap orig cx cy radius)
    (element_grid style peakmap radius density)
