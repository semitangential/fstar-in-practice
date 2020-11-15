module WaterTank.Controller

open WaterTank
open WaterTank.Controller.Raw

val counting_lemma: l:list bool -> a:bool ->
            Lemma (requires length l > 0 /\ (forall i. index l i = a))
                  (ensures count a l = length l)
let rec counting_lemma l a = match l with
  | h :: [] -> assert (index l 0 = a)
  | h :: tl -> assert (forall (i:nat{i+1 < length l}). index l (i+1) = index tl i);
             assert (index l 0 = a);
             assert (count a l = 1 + count a tl);
             counting_lemma tl a

val increasing_count_lemma: l1: list bool -> l2: list bool{length l1 = length l2} ->
              Lemma (requires forall j. (index l1 j = true) ==> (index l2 j = true))
                    (ensures count true l2 >= count true l1)
let rec increasing_count_lemma l1 l2 = match l1, l2 with
  | h1 :: tl1, h2 :: tl2 -> assert (h1 = index l1 0);
                         assert (forall k. (index tl1 k = index l1 (k + 1)));
                         assert (forall k. (index tl1 k = true) ==> (index tl2 k = true));
                         increasing_count_lemma tl1 tl2;
                         assert (count true l2 >= count true l1)
  | [], [] -> ()

val pointwise_list_equality_lemma: l1: list bool -> l2: list bool{length l1 = length l2} ->
              Lemma (requires forall i. (index l1 i = index l2 i))
                    (ensures l1 = l2)
let rec pointwise_list_equality_lemma l1 l2 = match l1, l2 with
  | [], [] -> ()
  | h1 :: tl1, h2 :: tl2 ->
    assert (index l1 0 = h1 /\ index l2 0 = h2);
    assert (h1 = h2);
    
    assert (forall j. (index tl1 j = index l2 (j+1)));
    pointwise_list_equality_lemma tl1 tl2;
    assert (tl1 = tl2)

val decreasing_count_lemma: l1: list bool -> l2: list bool{length l1 = length l2} -> i:nat{i < length l1} ->
                  Lemma (requires forall j. (i = j \/ index l1 j = index l2 j))
                        (ensures count true l2 >= (count true l1) - 1)
let rec decreasing_count_lemma l1 l2 i = match l1, l2 with
  | h1 :: tl1, h2 :: tl2 ->
    assert (forall j. (index tl1 j = index l1 (j+1)));
    match i with
      | 0 ->
        assert (forall j. (index tl1 j = index tl2 j));
        pointwise_list_equality_lemma tl1 tl2;
        assert (tl1 = tl2);
        assert (count true tl1 = count true tl2)
      | _ ->
        assert (h1 = index l1 0 /\ h2 = index l2 0);
        assert (h1 = h2);
        decreasing_count_lemma tl1 tl2 (i-1)

val non_overflowing: state -> bool
let non_overflowing vs = match vs with
  vi :: vos -> (not vi) || count true vos >= 2

val all_open_is_non_overflowing: vs: state ->
                 Lemma (requires (forall i. (index vs i) = true))
                       (ensures non_overflowing vs)
let all_open_is_non_overflowing vs = match vs with
  vi :: vos ->
  assert (forall (i:nat{i+1 < length vs}). index vs (i+1) = index vos i);
  counting_lemma vos true;
  assert (count true vos = length vos);
  assert (non_overflowing vs)

assume val get_tank_state: unit -> Tank (FStar.Ghost.erased state)
                                (fun vs0 -> True)
                                (fun vs0 x vs1 -> vs0 = FStar.Ghost.reveal x /\ vs0 = vs1)

val open_all: unit -> Tank unit
                          (fun _ -> True)
                          (fun _ _ vs1 -> (non_overflowing vs1) /\
                                       (forall i. (index vs1 i) = true))
let open_all () = open_all' ();
  let vs = get_tank_state () in (
    all_open_is_non_overflowing vs;
    assert (non_overflowing vs))

val close_all: unit -> Tank unit 
                           (fun _ -> True)
                           (fun _ _ vs1 -> (non_overflowing vs1) /\
                                        (forall i. (index vs1 i) = false))
let close_all () = close_all' ();
  let vs = get_tank_state () in (
    assert (index vs 0 = false)
  )

val open_valve: i: valve -> Tank unit
            (fun vs -> non_overflowing vs
                  /\ index vs i = false
                  /\ (i > 0 \/ count true (tail vs) >= 2))
            (fun vs0 _ vs1 -> non_overflowing vs1
                  /\ index vs1 i = true
                  /\ (forall j. i = j \/ index vs0 j = index vs1 j))
let open_valve i =
  let vs1 = get_tank_state () in
  open_valve' i;
  let vs2 = get_tank_state () in
  assert (i > 0 /\ index vs1 0 = false ==> index vs2 0 = false /\ non_overflowing vs2);

  assert (forall j. ((index vs1 j = true) ==> (index vs2 j = true)));
  assert (forall j. index (tail vs1) j = index vs1 (j+1));
  assert (forall j. ((index (tail vs1) j = true) ==> (index (tail vs2) j = true)));
  increasing_count_lemma (tail vs1) (tail vs2)

val close_valve: i: valve -> Tank unit
              (fun vs -> non_overflowing vs
                    /\ index vs i = true
                    /\ (i = 0 \/ count true (tail vs) >= 3))
              (fun vs0 _ vs1 -> non_overflowing vs1
                           /\ index vs1 i = false
                           /\ (forall j. i = j \/ index vs0 j = index vs1 j))
let close_valve i =
  let vs1 = get_tank_state () in
  close_valve' i;
  let vs2 = get_tank_state () in
  match i with
    | 0 -> assert (non_overflowing vs1)
    | _ ->
      assert (forall j. (index (tail vs1) j = index vs1 (j+1)));
      decreasing_count_lemma (tail vs1) (tail vs2) (i-1);
      assert (1 + count true (tail vs2) = count true (tail vs1))
