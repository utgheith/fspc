module ParserCombinators

(* For an example of each combinator, see ParserCombinators.Examples.fst,
   where they are checked by evaluation. *)

open FStar.List.Tot
open FStar.Char

(* The message for a `NoMatch` that a `cut` turned into a `Fail`. *)
let cut_message = "unexpected input"

(* An error recorded at the point where `rest` remains. *)
let error_at (message:string) (rest:list 't) : error =
  { message; remaining = length rest }

(*** Monad *)

let return x =
  fun inp -> (Ok { value = x; committed = false }, inp, [])

let no_match =
  fun inp -> (NoMatch, inp, [])

let fail msg =
  fun inp -> (Fail { msg }, inp, [])

let bind p f =
  fun inp ->
    match p inp with
    | (NoMatch, r1, es1) -> (NoMatch, r1, es1)
    | (Fail { msg }, r1, es1) -> (Fail { msg }, r1, es1)
    | (Ok { value = x; committed = k1 }, r1, es1) ->
      match f x r1 with
      | (Ok { value = y; committed = k2 }, r2, es2) ->
        (Ok { value = y; committed = k1 || k2 }, r2, es1 @ es2)
      | (NoMatch, r2, es2) ->
        if k1  (* past a cut: commit *)
        then (Fail { msg = cut_message }, r2, es1 @ es2)
        else (NoMatch, r2, es1 @ es2)
      | (Fail { msg }, r2, es2) -> (Fail { msg }, r2, es1 @ es2)

let ( let* ) p f =
  bind p f

let map f p =
  fun inp ->
    match p inp with
    | (Ok { value = x; committed = k }, r, es) -> (Ok { value = f x; committed = k }, r, es)
    | (NoMatch, r, es) -> (NoMatch, r, es)
    | (Fail { msg }, r, es) -> (Fail { msg }, r, es)

let ( <|> ) p q =
  fun inp ->
    match p inp with
    | (Ok { value = x }, r, es) -> (Ok { value = x; committed = false }, r, es)  (* cuts end here *)
    | (Fail { msg }, r, es) -> (Fail { msg }, r, es)
    | (NoMatch, _, _) ->  (* `p` was speculative: drop its errors *)
      match q inp with
      | (Ok { value = x }, r, es) -> (Ok { value = x; committed = false }, r, es)
      | (NoMatch, r, es) -> (NoMatch, r, es)
      | (Fail { msg }, r, es) -> (Fail { msg }, r, es)

let weaken p =
  fun inp ->
    match p inp with
    | (Ok { value = x; committed = k }, r, es) -> (Ok { value = x; committed = k }, r, es)
    | (NoMatch, r, es) -> (NoMatch, r, es)
    | (Fail { msg }, r, es) -> (Fail { msg }, r, es)

let rec choice ps =
  match ps with
  | [] -> no_match
  | p :: ps' -> p <|> choice ps'

(*** Cuts *)

let cut =
  fun inp -> (Ok { value = (); committed = true }, inp, [])

let attempt p =
  fun inp ->
    match p inp with
    | (Ok { value = x }, r, es) -> (Ok { value = x; committed = false }, r, es)
    | (NoMatch, r, es) -> (NoMatch, r, es)
    | (Fail _, r, es) -> (NoMatch, r, es)

let expect what p =
  fun inp ->
    match p inp with
    | (Ok { value = x; committed = k }, r, es) -> (Ok { value = x; committed = k }, r, es)
    | (NoMatch, r, es) -> (Fail { msg = "expected " ^ what }, r, es)
    | (Fail { msg }, r, es) -> (Fail { msg }, r, es)

let or_fail #t #a msg p =
  p <|> fail msg

(*** Primitives *)

let satisfy_map f =
  fun inp ->
    match inp with
    | x :: r ->
      (match f x with
       | Some y -> (Ok { value = y; committed = false }, r, [])
       | None -> (NoMatch, inp, []))
    | [] -> (NoMatch, inp, [])

let any_token #t =
  satisfy_map Some

let satisfy pred =
  satisfy_map (fun x -> if pred x then Some x else None)

let exactly x =
  satisfy (fun y -> y = x)

let eof =
  fun inp ->
    match inp with
    | [] -> (Ok { value = (); committed = false }, inp, [])
    | _ -> (NoMatch, inp, [])

let peek =
  fun inp ->
    match inp with
    | x :: _ -> (Ok { value = Some x; committed = false }, inp, [])
    | [] -> (Ok { value = None; committed = false }, inp, [])

let peek_n n =
  fun inp -> (Ok { value = fst (splitAt n inp); committed = false }, inp, [])

let here =
  fun inp -> (Ok { value = length inp; committed = false }, inp, [])

(*** Repetition *)

let rec many p inp =
  match p inp with
  | (NoMatch, _, _) -> (Ok { value = []; committed = false }, inp, [])
  | (Fail { msg }, r1, es1) -> (Fail { msg }, r1, es1)
  | (Ok { value = x }, r1, es1) ->
    match many p r1 with
    | (Ok { value = xs }, r2, es2) -> (Ok { value = x :: xs; committed = false }, r2, es1 @ es2)
    | (NoMatch, r2, es2) -> (NoMatch, r2, es1 @ es2)
    | (Fail { msg }, r2, es2) -> (Fail { msg }, r2, es1 @ es2)

let rec many_state p st inp =
  match p st inp with
  | (NoMatch, _, _) -> (Ok { value = []; committed = false }, inp, [])
  | (Fail { msg }, r1, es1) -> (Fail { msg }, r1, es1)
  | (Ok { value = (x, st') }, r1, es1) ->
    match many_state p st' r1 with
    | (Ok { value = xs }, r2, es2) -> (Ok { value = x :: xs; committed = false }, r2, es1 @ es2)
    | (NoMatch, r2, es2) -> (NoMatch, r2, es1 @ es2)
    | (Fail { msg }, r2, es2) -> (Fail { msg }, r2, es1 @ es2)

let many1 p =
  let* x = p in
  let* xs = many p in
  return (x :: xs)

let optional p =
  map Some p <|> return None

let sep_by1 p sep =
  let* x = p in
  let* xs = many (let* _ = sep in p) in
  return (x :: xs)

let sep_by p sep =
  weaken (sep_by1 p sep) <|> return []

let between open_ close p =
  let* _ = open_ in
  let* x = p in
  let* _ = close in
  return x

(** Parse `(op p)*`, folding the results left-associatively onto `acc`. *)
val chainl_rest
        (p:parser 't 'a true)               // the operands
        (op:parser 't ('a -> 'a -> 'a) true)   // the operators
        (acc:'a)                            // the result so far
        (inp:list 't)                       // the input stream
        : Tot (result 't 'a false inp) (decreases (length inp))
let rec chainl_rest p op acc inp =
  match op inp with
  | (NoMatch, _, _) -> (Ok { value = acc; committed = false }, inp, [])
  | (Fail { msg }, r1, es1) -> (Fail { msg }, r1, es1)
  | (Ok { value = f; committed = k1 }, r1, es1) ->
    match p r1 with
    | (NoMatch, r2, es2) ->
      (* operator without operand: back off, unless `op` passed a cut *)
      if k1
      then (Fail { msg = cut_message }, r2, es1 @ es2)
      else (Ok { value = acc; committed = false }, inp, [])
    | (Fail { msg }, r2, es2) -> (Fail { msg }, r2, es1 @ es2)
    | (Ok { value = y }, r2, es2) ->
      match chainl_rest p op (f acc y) r2 with
      | (Ok { value = z }, r3, es3) ->
        (Ok { value = z; committed = false }, r3, es1 @ es2 @ es3)
      | (NoMatch, r3, es3) -> (NoMatch, r3, es1 @ es2 @ es3)
      | (Fail { msg }, r3, es3) -> (Fail { msg }, r3, es1 @ es2 @ es3)

let chainl1 p op =
  let* x = p in
  chainl_rest p op x

(*** Error recovery *)

let recover p skip default =
  fun inp ->
    match p inp with
    | (Fail { msg }, r1, es1) ->
      (match skip r1 with
       | (Ok _, r2, es2) ->
         (Ok { value = default; committed = false }, r2, es1 @ [error_at msg r1] @ es2)
       | _ -> (Fail { msg }, r1, es1))
    | other -> other

let skip_until stop =
  map (fun _ -> ()) (many (satisfy (fun x -> not (stop x))))

let skip_past stop =
  let* _ = skip_until stop in
  let* _ = satisfy stop in
  return ()

(*** Recursion *)

(** `fix_below f n` behaves like the fixpoint of `f` on inputs shorter than
    `n`, and doesn't match anything longer. Each unfolding hands `f` a copy
    of itself bounded by the current input length, so the recursion is on a
    strictly decreasing natural number. *)
val fix_below
        (#c:bool)                           // true -> the grammar consumes input
        (f:parser 't 'a c -> parser 't 'a c)  // the grammar, given itself
        (n:nat)                             // bound on the input length
        : Tot (parser 't 'a c) (decreases n)
let rec fix_below f n =
  fun inp ->
    if length inp < n
    then f (fix_below f (length inp)) inp
    else (NoMatch, inp, [])

let fix f =
  fun inp -> f (fix_below f (length inp)) inp

(*** Running *)

let run p inp =
  let full =
    let* x = p in
    let* _ = expect "end of input" eof in
    return x
  in
  match full inp with
  | (Ok { value = x }, _, es) -> (Some x, es)
  | (NoMatch, r, es) -> (None, es @ [error_at "no match" r])
  | (Fail { msg }, r, es) -> (None, es @ [error_at msg r])

(*** Character-level helpers (t = char) *)

let pchar c =
  exactly c

(** Exactly the characters `c :: cs`. *)
val pchars
        (c:char)          // the first character
        (cs:list char)    // the rest
        : Tot (parser char unit true) (decreases cs)
let rec pchars c cs =
  match cs with
  | [] -> map (fun _ -> ()) (pchar c)
  | d :: ds -> let* _ = pchar c in pchars d ds

let pstring s =
  match FStar.String.list_of_string s with
  | c :: cs -> map (fun _ -> s) (pchars c cs)
  | [] -> no_match

let recognize #c #a p =
  fun inp ->
    match p inp with
    | (Ok { committed = k }, rest, es) ->
      let n : nat = length inp - length rest in
      (Ok { value = FStar.String.string_of_list (fst (splitAt n inp)); committed = k }, rest, es)
    | (NoMatch, rest, es) -> (NoMatch, rest, es)
    | (Fail { msg }, rest, es) -> (Fail { msg }, rest, es)

let is_space x =
  x = ' ' || x = '\t' || x = '\n' || x = '\r'

let is_digit x =
  let n = FStar.Char.int_of_char x in
  48 <= n && n <= 57

let spaces = many (satisfy is_space)

let lexeme p =
  let* x = p in
  let* _ = spaces in
  return x

let symbol c =
  lexeme (pchar c)

let digit_value x =
  FStar.Char.int_of_char x - 48

let natural =
  map (fold_left (fun acc d -> 10 * acc + digit_value d) 0)
      (many1 (satisfy is_digit))

let parse #c p s =
  let inp = FStar.String.list_of_string s in
  match run (let* _ = spaces in p) inp with
  | (Some x, []) -> Inl x
  | (_, es) ->
    Inr (FStar.List.Tot.map
           (fun e -> "offset " ^ string_of_int (length inp - e.remaining) ^ ": " ^ e.message)
           es)

(*** Positions in text (t = char) *)

(* Does a line break end at the head of `cs`? (CR LF counts at the LF.) *)
let breaks_line (cs:list char) : bool =
  match cs with
  | '\r' :: '\n' :: _ -> false
  | c :: _ -> c = '\n' || c = '\r'
  | [] -> false

(** `line_col`, from `line` and `col` with `off` characters still to go. *)
val line_col_from
        (cs:list char)        // the text from here on
        (off line col:nat)    // offset still to go, and where we are
        : Tot (nat & nat) (decreases cs)
let rec line_col_from cs off line col =
  if off = 0 then (line, col)
  else match cs with
       | [] -> (line, col)
       | _ :: cs' ->
         if breaks_line cs then line_col_from cs' (off - 1) (line + 1) 0
         else line_col_from cs' (off - 1) line (col + 1)

let line_col inp offset =
  line_col_from inp offset 1 0

(** `annotate`, from offset `off` at `line` and `col`. *)
val annotate_from
        (cs:list char)          // the text from `off` on
        (off line col:nat)      // where `cs` starts
        (xs:list ('a & nat))    // items with their offsets
        : Tot (list ('a & nat & nat)) (decreases %[cs; xs])
let rec annotate_from #a cs off line col xs =
  match xs with
  | [] -> []
  | (x, o) :: rest ->
    if o <= off || Nil? cs
    then (x, line, col) :: annotate_from cs off line col rest
    else match cs with
         | _ :: cs' ->
           if breaks_line cs then annotate_from cs' (off + 1) (line + 1) 0 xs
           else annotate_from cs' (off + 1) line (col + 1) xs

let annotate #a inp xs =
  annotate_from inp 0 1 0 xs

let offset_of inp remaining =
  if remaining <= length inp then length inp - remaining else 0

let format_error inp e =
  let (l, c) = line_col inp (offset_of inp e.remaining) in
  "line " ^ string_of_int l ^ ", column " ^ string_of_int c ^ ": " ^ e.message
