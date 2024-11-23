let verbose = ref false
let quiet = ref false

let debug fmt = (if !verbose then Printf.printf fmt else Printf.ifprintf stdout fmt)
let info fmt = (if not !quiet then Printf.printf fmt else Printf.ifprintf stdout fmt)
