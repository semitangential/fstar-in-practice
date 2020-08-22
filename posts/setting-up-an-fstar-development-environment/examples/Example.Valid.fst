module Example.Valid

val fibonacci: n:int{n >= 0} -> m:int{m > 0}
let rec fibonacci n = if n <= 1 then 1 else (fibonacci (n - 1)) + (fibonacci (n-2))
