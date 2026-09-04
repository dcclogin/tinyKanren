// Examples and tests for "MK", the TypeScript tinyKanren.
//
// Every case states the query, the expected answers as they are
// printed, and (for the divergent relations) the bound that makes the
// query finite.  The runner runs them all and reports.
//
//   node Examples.ts

import {
  type Goal,
  type Term,
  conde,
  cons,
  eq,
  exist,
  fail,
  list,
  nil,
  run,
  runAll,
  show,
  succeed,
  sym,
  trace,
} from "./MK.ts";

//------------------------- relations ------------------------

const nullo = (l: Term): Goal => eq(l, nil);

const conso = (a: Term, d: Term, p: Term): Goal => eq(cons(a, d), p);

const caro = (p: Term, a: Term): Goal => exist((d) => [conso(a, d, p)]);

const cdro = (p: Term, d: Term): Goal => exist((a) => [conso(a, d, p)]);

function appendo(l: Term, s: Term, out: Term): Goal {
  return conde(
    [nullo(l), eq(s, out)],
    [
      exist((a, d, res) => [
        conso(a, d, l),
        conso(a, res, out),
        appendo(d, s, res),
      ]),
    ],
  );
}

function membero(x: Term, l: Term): Goal {
  return exist((a, d) => [
    conso(a, d, l),
    conde([eq(x, a)], [membero(x, d)]),
  ]);
}

function reverso(l: Term, out: Term): Goal {
  return conde(
    [nullo(l), nullo(out)],
    [
      exist((a, d, res) => [
        conso(a, d, l),
        reverso(d, res),
        appendo(res, list(a), out),
      ]),
    ],
  );
}

// Unary numbers: z, (s z), (s (s z)), ...
const zero: Term = sym("z");

const succo = (n: Term): Term => list(sym("s"), n);

function peano(n: number): Term {
  let t = zero;
  for (let i = 0; i < n; i++) t = succo(t);
  return t;
}

function pluso(n: Term, m: Term, out: Term): Goal {
  return conde(
    [eq(n, zero), eq(m, out)],
    [
      exist((n2, out2) => [
        eq(n, succo(n2)),
        eq(out, succo(out2)),
        pluso(n2, m, out2),
      ]),
    ],
  );
}

// The two relations that make interleaving observable: `alwayso'
// succeeds infinitely often, `nevero' never succeeds and never stops.
// Both are knots tied through `conde', whose suspension keeps the
// recursive occurrence unforced; the eta-expansion is what keeps the
// definition itself from diverging.
const alwayso: Goal = (s) => conde([succeed], [alwayso])(s);

const nevero: Goal = (s) => conde([nevero])(s);

//--------------------------- cases ---------------------------

// Declared rather than imported: the repository has no package.json,
// so `@types/node' is not available.
declare const process: { exit(code: number): void };

interface Case {
  what: string;
  got: Term[];
  want: string[];
}

const cases: Case[] = [
  //---------------------------------------------------- unification
  {
    what: "q is 5",
    got: runAll((q) => [eq(q, 5)]),
    want: ["5"],
  },
  {
    what: "5 is q (symmetric)",
    got: runAll((q) => [eq(5, q)]),
    want: ["5"],
  },
  {
    what: "no answers",
    got: runAll((_q) => [fail]),
    want: [],
  },
  {
    what: "succeed leaves q fresh",
    got: runAll((_q) => [succeed]),
    want: ["_0"],
  },
  {
    what: "conflicting equations fail",
    got: runAll((q) => [eq(q, 5), eq(q, 6)]),
    want: [],
  },
  {
    what: "the same equation twice",
    got: runAll((q) => [eq(q, 5), eq(q, 5)]),
    want: ["5"],
  },
  {
    what: "atoms of every kind",
    got: runAll((q) => [eq(q, list(sym("a"), "b", 3, true, false, nil))]),
    want: ['(a "b" 3 #t #f ())'],
  },
  {
    what: "an improper list",
    got: runAll((q) => [eq(q, cons(1, 2))]),
    want: ["(1 . 2)"],
  },
  {
    what: "structural unification",
    got: runAll((q) => [
      exist((x, y) => [eq(list(x, 2), list(1, y)), eq(q, list(x, y))]),
    ]),
    want: ["(1 2)"],
  },
  {
    what: "occurs freely: q is bound to a variable, not a value",
    got: runAll((q) => [exist((x) => [eq(q, x)])]),
    want: ["_0"],
  },

  //------------------------------------------------------- reify
  {
    what: "distinct fresh variables get distinct names",
    got: runAll((q) => [exist((x, y) => [eq(q, list(x, y))])]),
    want: ["(_0 _1)"],
  },
  {
    what: "sharing is visible in the reified answer",
    got: runAll((q) => [exist((x, y) => [eq(q, list(x, y, x))])]),
    want: ["(_0 _1 _0)"],
  },
  {
    what: "a variable equated with another is reified once",
    got: runAll((q) => [exist((x, y) => [eq(x, y), eq(q, list(x, y))])]),
    want: ["(_0 _0)"],
  },
  {
    what: "reification walks under pairs",
    got: runAll((q) => [exist((x, y) => [eq(q, cons(list(x, 1), y))])]),
    want: ["((_0 1) . _1)"],
  },

  //------------------------------------------------------- conde
  {
    what: "three clauses, three answers",
    got: runAll((q) => [conde([eq(q, 1)], [eq(q, 2)], [eq(q, 3)])]),
    want: ["1", "2", "3"],
  },
  {
    what: "a failing clause is skipped",
    got: runAll((q) => [conde([fail], [eq(q, 2)], [fail], [eq(q, 4)])]),
    want: ["2", "4"],
  },
  {
    what: "conde is a disjunction of conjunctions",
    got: runAll((q) => [conde([eq(q, 1), fail], [eq(q, 2), succeed])]),
    want: ["2"],
  },
  // The four answers come out in the order the interleaving in `mplus'
  // produces them, which is not the clause order.
  {
    what: "nested conde multiplies the clauses",
    got: runAll((q) => [
      exist((x, y) => [
        conde([eq(x, 1)], [eq(x, 2)]),
        conde([eq(y, sym("a"))], [eq(y, sym("b"))]),
        eq(q, list(x, y)),
      ]),
    ]),
    want: ["(1 a)", "(1 b)", "(2 a)", "(2 b)"],
  },

  //------------------------------------------------------- caro/cdro
  {
    what: "caro of a list",
    got: runAll((q) => [caro(list(sym("a"), sym("b"), sym("c")), q)]),
    want: ["a"],
  },
  {
    what: "cdro of a list",
    got: runAll((q) => [cdro(list(sym("a"), sym("b"), sym("c")), q)]),
    want: ["(b c)"],
  },
  {
    what: "caro run backwards builds a list",
    got: runAll((q) => [caro(q, sym("a")), cdro(q, list(sym("b")))]),
    want: ["(a b)"],
  },

  //------------------------------------------------------- appendo
  {
    what: "appendo forwards",
    got: runAll((q) => [appendo(list(1, 2), list(3, 4), q)]),
    want: ["(1 2 3 4)"],
  },
  {
    what: "appendo with a fresh tail",
    got: runAll((q) => [
      exist((x) => [appendo(list(1), x, list(1, 2)), eq(q, x)]),
    ]),
    want: ["(2)"],
  },
  {
    what: "appendo backwards: every split of a three-element list",
    got: runAll((q) => [
      exist((x, y) => [
        appendo(x, y, list(sym("a"), sym("b"), sym("c"))),
        eq(q, list(x, y)),
      ]),
    ]),
    want: ["(() (a b c))", "((a) (b c))", "((a b) (c))", "((a b c) ())"],
  },
  {
    what: "appendo with both arguments fresh is infinite",
    got: run(4, (q) => [
      exist((x, y, z) => [appendo(x, y, z), eq(q, list(x, y, z))]),
    ]),
    want: [
      "(() _0 _0)",
      "((_0) _1 (_0 . _1))",
      "((_0 _1) _2 (_0 _1 . _2))",
      "((_0 _1 _2) _3 (_0 _1 _2 . _3))",
    ],
  },

  //------------------------------------------------------- membero
  {
    what: "membero enumerates the elements",
    got: runAll((q) => [membero(q, list(1, 2, 3))]),
    want: ["1", "2", "3"],
  },
  {
    what: "membero as a test: present",
    got: runAll((q) => [membero(2, list(1, 2, 3)), eq(q, true)]),
    want: ["#t"],
  },
  {
    what: "membero as a test: absent",
    got: runAll((q) => [membero(9, list(1, 2, 3)), eq(q, true)]),
    want: [],
  },
  {
    what: "membero repeats a repeated element",
    got: runAll((q) => [membero(q, list(sym("a"), sym("b"), sym("a")))]),
    want: ["a", "b", "a"],
  },
  {
    what: "two memberos intersect",
    got: runAll((q) => [membero(q, list(1, 2, 3)), membero(q, list(3, 4, 1))]),
    want: ["1", "3"],
  },
  {
    what: "membero of a fresh list is infinite",
    got: run(3, (q) => [membero(sym("x"), q)]),
    want: ["(x . _0)", "(_0 x . _1)", "(_0 _1 x . _2)"],
  },

  //------------------------------------------------------- reverso
  {
    what: "reverso forwards",
    got: runAll((q) => [reverso(list(1, 2, 3), q)]),
    want: ["(3 2 1)"],
  },
  {
    what: "reverso backwards",
    got: run(1, (q) => [reverso(q, list(1, 2, 3))]),
    want: ["(3 2 1)"],
  },

  //------------------------------------------------------- arithmetic
  {
    what: "2 + 3 = 5",
    got: runAll((q) => [pluso(peano(2), peano(3), q)]),
    want: ["(s (s (s (s (s z)))))"],
  },
  {
    what: "5 - 2 = 3 (subtraction is addition backwards)",
    got: runAll((q) => [pluso(peano(2), q, peano(5))]),
    want: ["(s (s (s z)))"],
  },
  {
    what: "every pair summing to 3",
    got: runAll((q) => [
      exist((x, y) => [pluso(x, y, peano(3)), eq(q, list(x, y))]),
    ]),
    want: [
      "(z (s (s (s z))))",
      "((s z) (s (s z)))",
      "((s (s z)) (s z))",
      "((s (s (s z))) z)",
    ],
  },
  {
    what: "addition with both summands fresh is infinite",
    got: run(3, (q) => [
      exist((x, y, z) => [pluso(x, y, z), eq(q, list(x, y, z))]),
    ]),
    want: ["(z _0 _0)", "((s z) _0 (s _0))", "((s (s z)) _0 (s (s _0)))"],
  },

  //------------------------------------------------------- interleaving
  {
    what: "run bounds an infinite stream",
    got: run(3, (q) => [alwayso, eq(q, true)]),
    want: ["#t", "#t", "#t"],
  },
  {
    what: "a finite branch is not starved by an infinite one",
    got: run(3, (q) => [conde([eq(q, true)], [alwayso]), eq(q, false)]),
    want: ["#f", "#f", "#f"],
  },
  {
    what: "a divergent branch does not hide an answer in another",
    got: run(1, (q) => [conde([nevero], [eq(q, sym("found"))])]),
    want: ["found"],
  },
  {
    what: "a divergent branch on either side",
    got: run(1, (q) => [conde([eq(q, sym("found"))], [nevero])]),
    want: ["found"],
  },
  {
    what: "asking for none of an infinite stream terminates",
    got: run(0, (_q) => [alwayso]),
    want: [],
  },
];

//--------------------------- runner ---------------------------

function report(c: Case): boolean {
  const actual = c.got.map(show);
  if (actual.length === c.want.length && actual.every((a, i) => a === c.want[i])) {
    console.log(`ok   ${c.what}  =>  ${actual.join(" ")}`);
    return true;
  }
  console.log(`FAIL ${c.what}`);
  console.log(`       want: ${c.want.join(" ")}`);
  console.log(`       got:  ${actual.join(" ")}`);
  return false;
}

// `trace' prints as it goes, so it is shown rather than checked: the
// goal itself only succeeds.
function demoTrace(): void {
  console.log("\ntrace:");
  const answers = runAll((q) => [
    exist((x, y) => [eq(x, 1), trace("  x, y = ", x, y), eq(q, list(x, y))]),
  ]);
  console.log(answers.map(show).join(" "));
}

const failed = cases.filter((c) => !report(c)).length;
console.log("");
console.log(`${cases.length - failed} / ${cases.length} passed`);
demoTrace();
if (failed !== 0) process.exit(1);
