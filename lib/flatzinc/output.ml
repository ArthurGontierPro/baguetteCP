(* The standard FlatZinc output format (SPEC 2.2).

   A pure function from a [Model.t] plus one assignment to the bytes that go on stdout.
   It touches nothing from Baguette_core or Baguette_proof on purpose: the printer is the
   last thing between a solution and the user, and it should be testable — byte for byte,
   against test/expected/*.out — without standing a solver up first.

   The exact bytes are ground truth under I-M1: test/expected/*.out is not adjusted to
   match this module, this module is adjusted to match it. What those files pin down, and
   the spec does not spell out, is that there is no blank line and no trailing space
   anywhere: a solution is exactly `name = value;\n' per output item followed by
   `----------\n', and every line including the last is newline-terminated. *)

(* Rendering a value needs the variable's *declared* domain, because "1" and "true" are
   the same assignment printed under two different types, and only the declaration says
   which. [Const] operands lose that distinction: the builder folds a bool parameter to
   0/1 while resolving names, and by the time an output item reaches here its boolness is
   not recoverable. So a `Const` prints as a decimal integer even when it came from a
   `bool` parameter. That is a known limitation of the Model.t representation, not a
   guess made here; fixing it means carrying the type on the operand, which is a change
   to model.ml that no current test needs. *)

let bool_string v =
  if v = 0 then "false"
  else if v = 1 then "true"
  else
    (* A `var bool' holding something other than 0 or 1 means the store or a propagator
       is broken. Printing "true" for 2 would launder that bug into a plausible-looking
       answer, which is precisely what I-S1 exists to prevent. *)
    invalid_arg (Printf.sprintf "Output: bool variable has non-Boolean value %d" v)

let render (m : Model.t) (values : int array) (op : Model.operand) =
  match op with
  | Model.Const n -> string_of_int n
  | Model.Var i -> (
      if i < 0 || i >= Model.nvars m || i >= Array.length values then
        invalid_arg (Printf.sprintf "Output: variable index %d out of range" i)
      else
        match (Model.var m i).Model.v_dom with
        | Model.Dbool -> bool_string values.(i)
        | Model.Drange _ | Model.Dset _ -> string_of_int values.(i))

let string_of_range (l, u) = Printf.sprintf "%d..%d" l u

let item (m : Model.t) values (it : Model.output_item) =
  match it with
  | Model.Out_var (name, op) -> Printf.sprintf "%s = %s;\n" name (render m values op)
  | Model.Out_array (name, dims, ops) ->
      (* `x = array1d(1..3, [1, 2, 3]);' — the index ranges come first, one per
         dimension, then the elements in row-major order as a single flat list. The
         dimension count in the function name is the length of [dims], so a zero-
         dimensional item (which FlatZinc has no syntax for, but the type admits) degrades
         to `array0d([...])' rather than emitting a stray separator. *)
      let elems = "[" ^ String.concat ", " (List.map (render m values) ops) ^ "]" in
      let args = List.map string_of_range dims @ [ elems ] in
      Printf.sprintf "%s = array%dd(%s);\n" name (List.length dims)
        (String.concat ", " args)

(* The separator after every solution. `==========' (exhausted) is *additional* to this
   and is printed by the caller, not folded in here: whether the space was exhausted is
   the search's business, not the printer's. *)
let separator = "----------\n"

let solution (m : Model.t) (values : int array) : string =
  let b = Buffer.create 128 in
  List.iter (fun it -> Buffer.add_string b (item m values it)) m.Model.output;
  Buffer.add_string b separator;
  Buffer.contents b

let unsatisfiable = "=====UNSATISFIABLE=====\n"
let exhausted = "==========\n"
