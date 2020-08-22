module Example.Invalid

val fibonacci: n:int{n >= 0} -> m:int{m > n}
let rec fibonacci n = if n <= 1 then 1 else (fibonacci (n - 1)) + (fibonacci (n-2))
