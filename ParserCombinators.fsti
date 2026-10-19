module ParserCombinators

(* A small, total parser-combinator library, generic in the token type.

   `parser t a c` is a parser parameterized by:

        - `t`: the type of input tokens (e.g., `char`)
        - `a`: the type of the result (e.g. `ast`)
        - `c`: a boolean indicating whether the parser consumes input
                true -> length out < length inp
                false -> length out <= length inp

   For an example of each combinator, see ParserCombinators.Examples.fst,
   where they are checked by evaluation.

 *)

open FStar.List.Tot
open FStar.Char


(** Does going from `inp` to `rest` respect the consumption guarantee `c`? *)
let consumed
        (c:bool)         // true -> must consume input
        (inp:list 't)    // the input before parsing
        (rest:list 't)   // the input left over after parsing
        : bool
        = if c then length rest < length inp else length rest <= length inp

(** What a parser concluded, without the remaining input. *)
type outcome (a:Type0): Type  =
  | Ok { value:a; committed:bool } // success, comitted = true ==> no backtracking 
  | NoMatch         // failure, but another alternative may succeed
  | Fail { msg:string }   // failure, no alternative will succeed


(** An error that parsing recovered from (or the one that stopped it). *)
type error = {
        message:string;     // what went wrong
        remaining:nat       // length of the input remaining at the error
    }

(** does the outcome respect the consumption guarantee? *)
let valid
        (c:bool)                                // true -> success must consume input
        (inp:list 't)                           // the input before parsing
        (r:outcome 'a & list 't & list error)   // outcome, remaining input, errors
        : bool
        = match r with
          | (o, rest, _) -> consumed (c && Ok? o) inp rest

(* The result of running a parser on `inp`, with the remaining input and
   the errors recovered from along the way. *)
let result
        (t:Type)       // the token type
        (a:Type)       // the result type
        (c:bool)        // true -> consumes input
        (inp:list t)    // the input stream
        :Type = r:(outcome a & list t & list error){valid c inp r}

(** A parser is a function from an input stream to a result *)
let parser (t:Type) (a:Type) (c:bool) = inp:list t -> result t a c inp

(*** Monad *)

(** Succeed with `x` without consuming anything. *)
val return
        (x:'a)        // the value to produce
        : parser 't 'a false

(** Never match, letting an enclosing `<|>` try something else. *)
val no_match
        (#c:bool)     // any consumption guarantee holds vacuously
        : parser 't 'a c

(** Fail outright with the message `msg`. *)
val fail
        (#c:bool)        // any consumption guarantee holds vacuously
        (msg:string)     // what went wrong
        : parser 't 'a c

(** Run `p`, then the parser chosen by `f` from its result.
    Sequencing consumes if either side consumes. If `p` passed a `cut`,
    a `NoMatch` from `f` becomes a `Fail`. *)
val bind
        (#c1:bool)                // true -> `p` consumes input
        (#c2:bool)                // true -> `f x` consumes input
        (p:parser 't 'a c1)       // the first parser
        (f:'a -> parser 't 'b c2) // picks the second parser from `p`'s result
        : parser 't 'b (c1 || c2)

(** `let* x = p in e` is `bind p (fun x -> e)`. *)
val ( let* )
        (#c1:bool)                // true -> `p` consumes input
        (#c2:bool)                // true -> `f x` consumes input
        (p:parser 't 'a c1)       // the first parser
        (f:'a -> parser 't 'b c2) // picks the second parser from `p`'s result
        : parser 't 'b (c1 || c2)

(** Apply `f` to the result of `p`. *)
val map
        (#c:bool)           // true -> `p` consumes input
        (f:'a -> 'b)        // the function to apply
        (p:parser 't 'a c)  // the parser to run
        : parser 't 'b c

(** Ordered choice: try `p`, and if it doesn't match try `q` on the same
    input. A `Fail` from `p` is final. The result is only guaranteed to
    consume if both alternatives do. Cuts inside `p` or `q` don't reach
    beyond this choice. *)
val ( <|> )
        (#c1:bool)           // true -> `p` consumes input
        (#c2:bool)           // true -> `q` consumes input
        (p:parser 't 'a c1)  // tried first
        (q:parser 't 'a c2)  // tried only if `p` fails
        : parser 't 'a (c1 && c2)

(** Forget a consumption guarantee. Why? to fake co-variance when needed *)
val weaken
        (#c:bool)           // the guarantee being forgotten
        (p:parser 't 'a c)  // the parser to weaken
        : parser 't 'a false

(** The first parser in `ps` that matches: `p1 <|> p2 <|> ... <|> no_match`. *)
val choice
        (ps:list (parser 't 'a true))     // the alternatives, in order
        : parser 't 'a true

(*** Cuts *)

(** Commit to the current alternative: from here on, a `NoMatch` in the
    same sequence becomes a `Fail`. *)
val cut
        : parser 't unit false

(** Undo commitment: a `Fail` from `p` becomes a `NoMatch`, so an
    enclosing `<|>` may try another alternative. *)
val attempt
        (#c:bool)           // true -> `p` consumes input
        (p:parser 't 'a c)  // the parser to run
        : parser 't 'a c

(** Require `p` to match: its `NoMatch` becomes `Fail "expected <what>"`. *)
val expect
        (#c:bool)           // true -> `p` consumes input
        (what:string)       // describes what `p` recognizes
        (p:parser 't 'a c)  // the required parser
        : parser 't 'a c

(** Require `p` to match: its `NoMatch` becomes `Fail msg`. *)
val or_fail
        (msg:string)           // the whole error message
        (p:parser 't 'a true)  // the required parser
        : parser 't 'a true

(*** Primitives *)

(** The one primitive that looks at a token: consume it if `f` accepts it,
    keeping whatever `f` extracts. *)
val satisfy_map
        (f:'t -> option 'a)  // `Some y` accepts the token, producing `y`
        : parser 't 'a true

(** Consume any single token. *)
val any_token
        : parser 't 't true

(** Consume a token satisfying `pred`. *)
val satisfy
        (pred:'t -> bool)   // which tokens to accept
        : parser 't 't true

(** Consume exactly the token `x`. *)
val exactly
        (#t:eqtype)    // type of input tokens (needs equality)
        (x:t)          // the expected token
        : parser t t true

(** Succeed only at the end of the input. *)
val eof
        : parser 't unit false

(** Look at the next token without consuming it; `None` at the end of the
    input. Never fails. *)
val peek
        : parser 't (option 't) false

(** Look at up to `n` tokens ahead without consuming them. Never fails. *)
val peek_n
        (n:nat)       // how many tokens to look at
        : parser 't (list 't) false

(** The length of the remaining input, which identifies the current
    position (as in `error.remaining`). Never fails. *)
val here
        : parser 't nat false

(*** Repetition *)

(** Zero or more `p`s, stopping at the first `NoMatch`; a `Fail` is
    final. `p` must consume input to guarantee termination. *)
val many
        (p:parser 't 'a true)  // the parser to repeat
        (inp:list 't)          // the input stream
        : Tot (result 't  (list 'a) false inp) (decreases (length inp))

(** Like `many`, but threads a state through the iterations. Has to consume in order to guarantee termination. *)
val many_state
        (p:'s -> parser 't ('a & 's) true) // the parser to repeat, given the state
        (st:'s)                         // the initial state
        (inp:list 't)                   // the input stream
        : Tot (result 't (list 'a) false inp) (decreases (length inp))

(** One or more `p`s. *)
val many1
        (p:parser 't 'a true)  // the parser to repeat
        : parser 't (list 'a) true

(** Zero or one `p`. *)
val optional
        (#c:bool)           // true -> `p` consumes input
        (p:parser 't 'a c)  // the optional parser
        : parser 't (option 'a) false

(** One or more `p`s separated by `sep`. *)
val sep_by1
        (#c:bool)                // true -> `p` consumes input
        (p:parser 't 'a c)       // the items
        (sep:parser 't 's true)  // the separator
        : parser 't (list 'a) c

(** Zero or more `p`s separated by `sep`. *)
val sep_by
        (#c:bool)                // true -> `p` consumes input
        (p:parser 't 'a c)       // the items
        (sep:parser 't 's true)  // the separator
        : parser 't (list 'a) false

(** `p` surrounded by `open_` and `close`, keeping only `p`'s result. *)
val between
        (#c2:bool)                 // true -> `close` consumes input
        (#c3:bool)                 // true -> `p` consumes input
        (open_:parser 't 'o true)  // the opening delimiter
        (close:parser 't 'e c2)    // the closing delimiter
        (p:parser 't 'a c3)        // the contents
        : parser 't 'a true

(** Parse `p (op p)*`, folding the results left-associatively. *)
val chainl1
        (p:parser 't 'a true)               // the operands
        (op:parser 't ('a -> 'a -> 'a) true)   // the operators
        : parser 't 'a true

(*** Error recovery *)

(** If `p` fails, record its error, resynchronize with `skip` (starting
    where `p` failed), and succeed with `default`. If `skip` doesn't
    match either, the original failure stands. `skip` must consume
    whenever `p` must, so `many (recover p skip d)` cannot loop. *)
val recover
        (#c:bool)                 // true -> `p` and `skip` consume input
        (p:parser 't 'a c)        // the parser that may fail
        (skip:parser 't unit c)   // how to resynchronize after a failure
        (default:'a)              // stands in for the value `p` didn't produce
        : parser 't 'a c

(** Skip tokens up to (not including) the first one satisfying `stop`. *)
val skip_until
        (#t:Type0)          // the token type
        (stop:t -> bool)    // where to stop
        : parser t unit false

(** Skip tokens up to and including the first one satisfying `stop`. *)
val skip_past
        (#t:Type0)          // the token type
        (stop:t -> bool)    // where to stop
        : parser t unit true

(*** Recursion *)

(** Tie the knot for a recursive grammar. Inside `f`, the recursive parser
    only succeeds on input strictly shorter than where `f` started, so every
    grammar that consumes something before recursing behaves exactly as
    expected (left recursion simply fails instead of looping). *)
val fix
        (#c:bool)                           // true -> the grammar consumes input
        (f:parser 't 'a c -> parser 't 'a c)  // the grammar, given itself
        : parser 't 'a c

(*** Running *)

(** Run `p` on the whole input, requiring that all of it is consumed.
    Returns the value (if parsing got that far) and every error, in order.
    A value with errors is a best guess built from `recover` defaults. *)
val run
        (#c:bool)           // true -> `p` consumes input
        (p:parser 't 'a c)  // the parser to run
        (inp:list 't)       // the input stream
        : option 'a & list error

(*********************)
(* Character helpers *)
(*********************)

(** Consume exactly the character `c`. *)
val pchar
        (c:char)    // the expected character
        : parser char char true

(** Consume exactly the characters of `s` (non-empty), producing `s`. *)
val pstring
        (s:string)    // the expected text
        : parser char string true

(** Run `p`, but produce the text it consumed instead of its result. *)
val recognize
        (#c:bool)              // true -> `p` consumes input
        (p:parser char 'a c)   // the parser to run
        : parser char string c

(** Is `x` a whitespace character? *)
val is_space
        (x:char)    // the character to test
        : bool

(** Is `x` a decimal digit? *)
val is_digit
        (x:char)    // the character to test
        : bool

(** Skip zero or more whitespace characters. *)
val spaces : parser char (list char) false

(** Run `p` and skip any trailing whitespace. *)
val lexeme
        (#c:bool)              // true -> `p` consumes input
        (p:parser char 'a c)   // the parser to run
        : parser char 'a c

(** Consume the character `c` and any trailing whitespace. *)
val symbol
        (c:char)    // the expected character
        : parser char char true

(** The numeric value of the digit `x`. *)
val digit_value
        (x:char)    // a decimal digit
        : int

(** A non-negative decimal integer. *)
val natural : parser char int true

(** Parse a whole string *)
val parse (#c:bool) (p:parser char 'a c) (s:string) : either 'a (list string)

(************************)
(*** Positions in text  *)
(************************)

(** The line (from 1) and column (from 0, in characters) at `offset` in
    `inp`. Line breaks are LF, CR, and CR LF. *)
val line_col
        (inp:list char)    // the text
        (offset:nat)       // characters from the start
        : nat & nat

(** Attach line and column to each item, given its offset into `inp`.
    The offsets must not decrease; then this is one pass over `inp`. *)
val annotate
        (inp:list char)          // the text
        (xs:list ('a & nat))     // items with their offsets
        : list ('a & nat & nat)

(** The offset in `inp` of a position given as remaining input length. *)
val offset_of
        (inp:list char)    // the text
        (remaining:nat)    // length of the input remaining at the position
        : nat

(** "line L, column C: message", for an error found while parsing `inp`. *)
val format_error
        (inp:list char)    // the text that was parsed
        (e:error)          // the error
        : string
