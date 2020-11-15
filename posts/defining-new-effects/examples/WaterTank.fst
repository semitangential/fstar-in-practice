module WaterTank

open FStar.Ghost
open FStar.List.Pure

let length = FStar.List.Tot.Base.length
let index = FStar.List.Tot.Base.index
let tail = FStar.List.Tot.Base.tail
let count = FStar.List.Tot.Base.count

let num_output_valves = 3

let valve = x:int{x >= 0 /\ x <= num_output_valves}

type state = l:list bool{length l = 1 + num_output_valves}

new_effect TANK = STATE_h state

unfold let pure_lift (a:Type) (wp:pure_wp a) =
  fun (p: a -> state -> Type) (x: state) -> wp (fun y -> p y x)
sub_effect PURE ~> TANK = pure_lift

effect Tank (a: Type)
            (pre: (state -> Type))
            (post: (state -> a -> state -> Type))
  =
  TANK a (fun p vs0 -> pre vs0 /\
            (forall x vs1 . pre vs0 /\ post vs0 x vs1 ==> p x vs1))
