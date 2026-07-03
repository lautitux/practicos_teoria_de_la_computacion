#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/lovelace:0.3.1": *

#set page(width: auto, height: auto)

#let t = sym.triangle.stroked.r

#let ass_1 = rule(
  label: [ass],
  rule(
    label: [var],
    [],
    $ "n" =>^(M_2) 0 [] $,
  ),
  $ M_2 #t "result" := "n" #t M_3 $,
)

#let while_0 = rule(
  label: [while-i],
  rule(
    label: [var],
    [],
    $ "ls'" =>^(M_2) "Nil" [] $,
  ),
  $ M_2 #t "while ls' is" { "Cons" ["x", "xs"] -> "ls'", "n" = "xs", S ["n"] } #t M_2 $,
)

#let sec_1 = rule(
  label: [sec],
  while_0,
  ass_1,
  $ M_2 #t "while ls' is {...} ; result" := "n" #t M_3 $,
)

#let ass_0 = rule(
  label: [ass],
  rule(
    label: [var],
    [],
    $ "ls" =>^(M_1) "Nil" [] $,
  ),
  rule(
    label: [cons],
    [],
    $ 0 [] =>^(M_1) 0 [] $,
  ),
  $ M_1 #t "ls'", "n" := "ls", 0[] #t M_2 $,
)

#let sec_0 = rule(
  label: [sec],
  ass_0,
  sec_1,
  $ M_1 #t "ls'", "n" := "ls", 0 []" ; ""while ls' is" {...}" ; ""result" := "n" #t M_3 $,
)

#let tree = rule(
  label: [loc],
  sec_0,
  $ M_0 #t "largoP" #t M_4 $,
)

#prooftree(tree)

// largo =
// local ls', n {
//    ls', n := ls, 0 [] ;
//    while ls' is {
//       Cons [x, xs] -> ls', n = xs, S [n]
//    } ;
//    result := n
// }

#v(1em)

#grid(columns: 2, column-gutter: 5em)[
  $
    & M_0 = ("ls", "Nil" []) \
    & M_1 = ("ls'", "null"), ("n", "null"), ("ls", "Nil" []) \
    & M_2 = ("ls'", "Nil" []), ("n", 0 []), ("ls", "Nil" []) \
    & M_3 = ("result", 0 []), ("ls'", "Nil" []), ("n", 0 []), ("ls", "Nil" []) \
    & M_4 = ("result", 0 []), ("ls", "Nil" []) \
  $
][
  largoP =
  #box(baseline: (at: top, shift: -1.4em))[
    #pseudocode-list[
      - *local* ls', n {
        - ls', n := ls, 0 [] ;
        - while ls' is {
          - Cons [x, xs] $->$ ls', n = xs, S [n]
        - } ;
        - result := n
      - }
    ]
  ]
]
