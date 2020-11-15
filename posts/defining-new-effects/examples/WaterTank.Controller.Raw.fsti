module WaterTank.Controller.Raw

open WaterTank

val open_all':
    unit ->
      Tank unit
        (fun _ -> True)
        (fun _ _ vs -> forall i. (index vs i) = true)

val close_all':
    unit ->
      Tank unit
        (fun _ -> True)
        (fun _ _ vs -> forall i. (index vs i) = false)

val open_valve':
    i: valve ->
      Tank unit
        (fun vs -> index vs i = false)
        (fun vs0 _ vs1 -> index vs1 i = true /\
          (forall j. i = j \/ index vs0 j = index vs1 j))

val close_valve':
    i: valve ->
      Tank unit
        (fun vs -> index vs i = true)
        (fun vs0 _ vs1 -> index vs1 i = false /\
          (forall j. i = j \/ index vs0 j = index vs1 j))
