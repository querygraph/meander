## 10. Index of OCaml features

Each feature is explained in the section listed, before its first use.

| Feature | Section |
|---|---|
| phrases, the toplevel's `- : type = value`, `(* comments *)` | 1 |
| `int`, `max_int`, `/`, `mod`, `float` and `+.`, `*.`, `/.` | 1 |
| tuples and their types `a * b` | 1 |
| `let`, `let … in`, `Printf.printf`, `%d`, `%s`, `%!`, `^` | 1 |
| destructuring `let q, r = …`, `let () = …`, `unit` | 1 |
| `bool`, `=`, `<>`, `&&`, `\|\|`, `not` | 1 |
| functions `let f a b = …`, `let … and …`, `<>` as exclusive or, `%b` | 2 |
| type inference, type variables `'a`, polymorphism | 2 |
| arrays `[\| … \|]`, `a.(i)`, `fun x -> e`, `List.for_all`, `List.init`, `Fun.id` | 2 |
| lists `[]`, `::`, `@`, `List.length`, `Array.of_list` | 3 |
| `function`, pattern matching, `let rec` | 3 |
| `List.filter`, `List.map`, `List.concat_map` | 3 |
| the pipeline operator `\|>` | 3 |
| `assert`, `for … do … done`, `;`, guards `when`, `_`, `print_endline`, `List.nth` | 4 |
| `List.filteri` | 4 |
| `Array.init`, `List.sort compare`, structural equality | 5 |
| `ref`, `!`, `:=`, `incr`, `decr`, `Array.make`, `a.(i) <- v`, `begin … end`, `if` | 6 |
| optional `?(x = v)` and labelled `~x` arguments | 6 |
| toplevel directives, `#use "topfind"`, `#require`, `Unix.gettimeofday`, `List.iter`, `fst` | 6 |
| variant types, constructors | 7 |
| records, field access, record patterns | 7 |
| `Printf.sprintf`, `String.concat`, `invalid_arg`, `List.mapi` | 7 |
| callbacks, matching on tuples | 7 |
| modules, `struct … end`, functors, `Hashtbl.Make`, `Hashtbl.hash_param` | 7 |
| `option`, `None`, `Some`, `Option.value`, `find_opt`, `replace`, `iter`, `create`, `length`, `List.rev` | 7 |
| `States.fold`, `List.iteri` | 7 |
| domains, `Domain.spawn`, `Domain.join`, `Domain.recommended_domain_count` | 8 |
| data races, `Atomic.make`, `Atomic.fetch_and_add`, `Mutex.create`, `Mutex.protect` | 8 |
| `lsr`, `land`, `Array.iteri` | 8 |
| OxCaml modes: `local`, `portable`, `contended`, `uncontended` | 9 |
| capsules, `With_mutex.with_lock`, `With_mutex.destroy` | 9 |
| the `Parallel` scheduler, parallel slices, `Portable.Atomic` | 9 |
| unboxed types `float#`, `int64#`, unboxed tuples `#( … )` | 9 |
