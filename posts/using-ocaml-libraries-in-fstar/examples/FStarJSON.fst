module FStarJSON

let main = FStar.IO.print_string (Yojson.Basic.pretty_to_string
    (Yojson.Basic.from_string (FStar.IO.input_line())))
