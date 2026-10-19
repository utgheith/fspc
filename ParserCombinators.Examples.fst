module ParserCombinators.Examples

(* Some verified examples of the using the parser combinators library *)

friend ParserCombinators
open FStar.Char
open FStar.String
open ParserCombinators

let check (#a:Type) (ok:a -> prop) (actual:a)
  : Pure unit (requires normalize (ok actual)) (ensures fun _ -> True) = ()

let check_eq (#a:Type) (actual expected:a)
  : Pure unit (requires normalize (actual == expected)) (ensures fun _ -> True) =
  check (fun x -> x == expected) actual

let check_parse (#a:eqtype) (#c:bool) (p:parser char a c) (input:string) (expected:either a (list string))
  : Pure unit (requires normalize (parse p input == expected)) (ensures fun _ -> True) =
  check_eq (parse p input) expected

(*** Monad *)

(* return *)
let _ = check_parse
  (return 1)
  ""
  (Inl 1)
let _ = check
  (fun r -> Inr? r)
  (parse (return 1) "x")

(* no_match (the annotation fixes `c`, which F* can't infer here) *)
let _ = check
  (fun r -> Inr? r)
  (parse (no_match <: parser char int false) "")

(* fail: `<|>` doesn't try `pchar 'a'` *)
let _ = check_parse
  ((fail "oops" <: parser char char true) <|> pchar 'a')
  "a"
  (Inr ["offset 0: oops"])

(* bind *)
let _ = check_parse
  (bind (pchar 'a') (fun x -> map (fun y -> [x; y]) (pchar 'b')))
  "ab"
  (Inl ['a'; 'b'])

(* let* *)
let _ = check_parse
  (let* x = natural in
   let* _ = pchar '+' in
   let* y = natural in
   return (x + y))
  "1+2"
  (Inl 3)

(* map *)
let _ = check_parse
  (map digit_value (satisfy is_digit))
  "7"
  (Inl 7)

(* <|> *)
let _ = check_parse
  (pchar 'a' <|> pchar 'b')
  "b"
  (Inl 'b')

(* weaken: both branches need the same type *)
let x_or_nothing (b:bool) : parser char char false =
  if b then weaken (pchar 'x') else return 'x'
let _ = check_parse
  (x_or_nothing true)
  "x"
  (Inl 'x')
let _ = check_parse
  (x_or_nothing false)
  ""
  (Inl 'x')

(* choice: `pstring "let"` reads the "l", then gives up at the "a" *)
let _ = check_parse
  (choice [pstring "let"; pstring "lambda"])
  "lambda"
  (Inl "lambda")

(*** Cuts *)

(* cut: the second branch isn't tried *)
let _ = check_parse
  ((let* _ = pchar 'a' in let* _ = cut in pchar 'b') <|>
   (let* _ = pchar 'a' in pchar 'c'))
  "ac"
  (Inr ["offset 1: unexpected input"])

(* attempt *)
let _ = check_parse
  (attempt (fail "oops" <: parser char char true) <|> pchar 'a')
  "a"
  (Inl 'a')

(* expect *)
let _ = check_parse
  (expect "digit" (satisfy is_digit))
  "x"
  (Inr ["offset 0: expected digit"])

(* or_fail *)
let _ = check_parse
  (or_fail "need a digit" (satisfy is_digit))
  "x"
  (Inr ["offset 0: need a digit"])

(*** Primitives *)

(* satisfy_map *)
let _ = check_parse
  (satisfy_map (fun c -> if is_digit c then Some (digit_value c) else None))
  "7"
  (Inl 7)

(* any_token *)
let _ = check_parse
  any_token
  "x"
  (Inl 'x')

(* satisfy *)
let _ = check_parse
  (satisfy is_digit)
  "7"
  (Inl '7')
let _ = check
  (fun r -> Inr? r)
  (parse (satisfy is_digit) "a")

(* exactly: works for any token type with equality *)
let _ = check_eq
  (run (exactly 3) [3])
  (Some 3, [])

(* eof *)
let _ = check_parse
  (map Some (pchar 'a') <|> map (fun _ -> None) eof)
  ""
  (Inl None)

(* peek *)
let _ = check_parse
  (let* c = peek in
   let* _ = many any_token in
   return c)
  "ab"
  (Inl (Some 'a'))

(* peek_n *)
let _ = check_parse
  (let* cs = peek_n 2 in
   let* _ = many any_token in
   return cs)
  "abc"
  (Inl ['a'; 'b'])

(* here *)
let _ = check_parse
  (let* _ = pchar 'a' in
   let* n = here in
   let* _ = many any_token in
   return n)
  "abc"
  (Inl 2)

(*** Repetition *)

(* many *)
let _ = check_parse
  (many (pchar 'a'))
  "aaa"
  (Inl ['a'; 'a'; 'a'])
let _ = check_parse
  (many (pchar 'a'))
  ""
  (Inl [])

(* many_state: digits, each larger than the one before *)
let rising =
  many_state (fun last ->
    satisfy_map (fun c ->
      if is_digit c && digit_value c > last
      then Some (digit_value c, digit_value c) else None)) (-1)
let _ = check_parse
  rising
  "135"
  (Inl [1; 3; 5])
let _ = check
  (fun r -> Inr? r)
  (parse rising "153")

(* many1 *)
let _ = check
  (fun r -> Inr? r)
  (parse (many1 (satisfy is_digit)) "")

(* optional *)
let int =
  let* s = optional (pchar '-') in
  let* n = natural in
  return (if Some? s then -n else n)
let _ = check_parse
  int
  "-5"
  (Inl (-5))
let _ = check_parse
  int
  "5"
  (Inl 5)

(* sep_by1 *)
let _ = check_parse
  (sep_by1 natural (pchar ','))
  "1,2,3"
  (Inl [1; 2; 3])

(* sep_by *)
let _ = check_parse
  (sep_by natural (pchar ','))
  ""
  (Inl [])

(* between *)
let _ = check_parse
  (between (pchar '[') (pchar ']') natural)
  "[42]"
  (Inl 42)

(* chainl1: (10 - 4) - 3 *)
let _ = check_parse
  (chainl1 natural (map (fun _ x y -> x - y) (pchar '-')))
  "10-4-3"
  (Inl 3)

(*** Error recovery *)

(* recover: the value is the default, and the error is still reported *)
let _ = check_eq
  (run (recover (expect "digit" (satisfy is_digit)) (skip_past (fun c -> c = ';')) '0')
       ['x'; ';'])
  (Some '0', [{ message = "expected digit"; remaining = 2 }])

(* skip_until *)
let _ = check_parse
  (let* _ = skip_until is_digit in natural)
  "ab12"
  (Inl 12)

(* skip_past *)
let _ = check_parse
  (let* _ = skip_past (fun c -> c = ';') in natural)
  "junk;7"
  (Inl 7)

(*** Recursion *)

(* fix: how deeply nested: "()" is 1, "(())" is 2, ... *)
let depth =
  fix (fun depth ->
    between (pchar '(') (pchar ')')
      (map (fun o -> match o with None -> 1 | Some d -> d + 1) (optional depth)))
let _ = check_parse
  depth
  "((()))"
  (Inl 3)

(*** Running *)

(* run *)
let _ = check_eq
  (run (pchar 'a') ['a'; 'b'])
  (None, [{ message = "expected end of input"; remaining = 1 }])

(*** Character-level helpers *)

(* pchar *)
let _ = check_parse
  (pchar 'a')
  "a"
  (Inl 'a')

(* pstring *)
let _ = check_parse
  (pstring "let")
  "let"
  (Inl "let")
let _ = check
  (fun r -> Inr? r)
  (parse (pstring "let") "lex")

(* recognize *)
let _ = check_parse
  (recognize (many1 (satisfy is_digit)))
  "042"
  (Inl "042")

(* is_space *)
let _ = check_eq
  (is_space '\t')
  true
let _ = check_eq
  (is_space 'a')
  false

(* is_digit *)
let _ = check_eq
  (is_digit '7')
  true
let _ = check_eq
  (is_digit 'a')
  false

(* spaces *)
let _ = check_parse
  (let* _ = pchar 'a' in
   let* _ = spaces in
   pchar 'b')
  "a  b"
  (Inl 'b')

(* lexeme *)
let _ = check_parse
  (many (lexeme natural))
  "1 2 3 "
  (Inl [1; 2; 3])

(* symbol *)
let _ = check_parse
  (between (symbol '(') (symbol ')') natural)
  "( 5) "
  (Inl 5)

(* digit_value *)
let _ = check_eq
  (digit_value '7')
  7

(* natural *)
let _ = check_parse
  natural
  "042"
  (Inl 42)

(* parse: leading whitespace is fine, leftovers are not *)
let _ = check_parse
  natural
  "  12"
  (Inl 12)
let _ = check_parse
  natural
  "12x"
  (Inr ["offset 2: expected end of input"])

(*** Positions in text *)

(* line_col *)
let _ = check_eq
  (line_col (list_of_string "ab\ncd") 4)
  (2, 1)

(* annotate *)
let _ = check_eq
  (annotate (list_of_string "ab\ncd") [('x', 1); ('y', 3)])
  [('x', 1, 1); ('y', 2, 0)]

(* offset_of *)
let _ = check_eq
  (offset_of (list_of_string "abcd") 1)
  3

(* format_error *)
let _ = check_eq
  (format_error (list_of_string "ab\ncd") { message = "oops"; remaining = 1 })
  "line 2, column 1: oops"
