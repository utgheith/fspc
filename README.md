# ParserCombinators

A small, total parser-combinator library for [F*](https://fstar-lang.org),
generic in the token type.

A `parser t a c` reads tokens of type `t` and produces an `a`. The flag `c`
records whether the parser consumes input when it succeeds. F* uses that flag
to prove that repetition (`many`) and recursion (`fix`) terminate.

## Files

- `ParserCombinators.fsti`: the documented interface, which also holds
  character helpers (`pchar`, `pstring`, `natural`, `parse`, ...)
- `ParserCombinators.fst`: the implementation
- `ParserCombinators.Examples.fst`: examples of each combinator, checked by
  normalization at verification time

## Building

```sh
make          # verify all modules (checked files go in _cache/)
make clean
```

Set `FSTAR` to choose the F* binary (default `fstar.exe`), and `FSTAR_FLAGS`
to pass extra flags.

## Example

```fstar
module MyExample   // needs an interface (MyExample.fsti) to use `friend`

friend ParserCombinators   // exposes the definitions so `assert_norm` can evaluate them
open ParserCombinators

let _ = assert_norm (parse (sep_by1 natural (symbol ',')) "1,2,3" == Inl [1; 2; 3])
```

## License

BSD 3-Clause. See `LICENSE`.
