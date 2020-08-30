open Yojson.Basic

let main () = output_string stdout
    (Yojson.Basic.pretty_to_string (Yojson.Basic.from_channel stdin))

let () = main ()
