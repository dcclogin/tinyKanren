// A TypeScript version of mk.rkt.
//
// The structure follows the Racket source section by section.  Four
// places had to be adapted rather than transliterated:
//
//   * Racket distinguishes fresh logic variables by `eq?' (struct
//     identity).  JavaScript object identity is the same notion, so
//     `Var' needs no counter: `new Var(...)' is a fresh variable and
//     `===' is `eq?'.
//
//   * `delay'/`force' are ordinary functions rather than a macro, so a
//     suspension is written `delay(() => e)'.  The thunk stays visible
//     in the stream: the interleaving in `mplus' works by *observing*
//     that a stream is suspended.
//
//   * There are no macros, so `exist', `conde' and `run' are functions:
//     the binders of `exist'/`run' are the parameters of a closure and
//     a conjunction is an array of goals.  The source names of those
//     parameters are recovered from the closure for display only; when
//     they cannot be read, positional names are used instead.
//
//   * `display-code'/`debug-display' printed the source of a `run'
//     form, which is not available without macros, and is dropped.
//
// Scheme atoms map to JavaScript as: symbol -> interned `symbol'
// (`sym("a")'), string -> string, number -> number, boolean -> boolean,
// '() -> null.

//--------------------- substitution ----------------------

export class Var {
  readonly name: string;
  constructor(name: string) {
    this.name = name;
  }
}

export class Pair {
  readonly car: Term;
  readonly cdr: Term;
  constructor(car: Term, cdr: Term) {
    this.car = car;
    this.cdr = cdr;
  }
}

export type Atom = symbol | string | number | boolean | null;
export type Term = Var | Atom | Pair;

// An association list of (variable . term), extended at the front.
export interface Frame {
  readonly x: Var;
  readonly v: Term;
  readonly rest: S;
}
export type S = Frame | null;

export const emptyS: S = null;

export function sizeS(s: S): number {
  let n = 0;
  for (let p = s; p !== null; p = p.rest) n++;
  return n;
}

export function extS(x: Var, v: Term, s: S): S {
  return { x, v, rest: s };
}

function assq(x: Var, s: S): Frame | null {
  for (let p = s; p !== null; p = p.rest) {
    if (p.x === x) return p;
  }
  return null;
}

export function walk(v: Term, s: S): Term {
  while (v instanceof Var) {
    const p = assq(v, s);
    if (p === null) return v;
    v = p.v;
  }
  return v;
}

export function walkStar(v: Term, s: S): Term {
  const w = walk(v, s);
  if (w instanceof Pair) {
    return new Pair(walkStar(w.car, s), walkStar(w.cdr, s));
  }
  return w;
}

// `false' rather than `null' is the failure of unification: the empty
// substitution is `null', and both would otherwise be falsy.
export function unify(u: Term, v: Term, s: S): S | false {
  u = walk(u, s);
  v = walk(v, s);
  if (u === v) return s;
  if (u instanceof Var) return extS(u, v, s);
  if (v instanceof Var) return extS(v, u, s);
  if (u instanceof Pair && v instanceof Pair) {
    const s1 = unify(u.car, v.car, s);
    return s1 === false ? false : unify(u.cdr, v.cdr, s1);
  }
  return false;
}

let namePrefix = "_";

export function setNamePrefix(s: string): void {
  namePrefix = s;
}

export function name(n: number): symbol {
  return Symbol.for(namePrefix + n);
}

export function reifyS(v: Term, s: S): S {
  const w = walk(v, s);
  if (w instanceof Var) return extS(w, name(sizeS(s)), s);
  if (w instanceof Pair) return reifyS(w.cdr, reifyS(w.car, s));
  return s;
}

export function reify(v: Term, s: S): Term {
  const w = walkStar(v, s);
  return walkStar(w, reifyS(w, emptyS));
}

//---------------------- composition ----------------------

// The stream is parameterised by what it carries; a goal instantiates
// it at `S', so a goal maps a substitution to a stream of substitutions.
export class SCons<A> {
  readonly head: A;
  readonly tail: Stream<A>;
  constructor(head: A, tail: Stream<A>) {
    this.head = head;
    this.tail = tail;
  }
}

export class Thunk<A> {
  readonly func: () => Stream<A>;
  constructor(func: () => Stream<A>) {
    this.func = func;
  }
}

export type Stream<A> = null | Thunk<A> | SCons<A>;
export type Goal = (s: S) => Stream<S>;

export function delay<A>(f: () => Stream<A>): Stream<A> {
  return new Thunk(f);
}

export function force<A>(th: Stream<A>): Stream<A> {
  return th instanceof Thunk ? th.func() : th;
}

export function bind<A, B>(g: (a: A) => Stream<B>, v: Stream<A>): Stream<B> {
  if (v === null) return null;
  if (v instanceof Thunk) return delay(() => bind(g, force(v)));
  return mplus(g(v.head), delay(() => bind(g, v.tail)));
}

export function bindStar(v: Stream<S>, ...gs: Goal[]): Stream<S> {
  for (const g of gs) v = bind(g, v);
  return v;
}

export function mplus<A>(v: Stream<A>, f: Stream<A>): Stream<A> {
  if (v === null) return f;
  if (v instanceof Thunk) return delay(() => mplus(f, force(v)));
  return new SCons(v.head, delay(() => mplus(f, v.tail)));
}

export function mplusStar<A>(...es: Stream<A>[]): Stream<A> {
  if (es.length === 0) return null;
  const [e, ...rest] = es;
  if (rest.length === 0) return e;
  return mplus(e, delay(() => mplusStar(...rest)));
}

//------------------- goal constructors -------------------

export const succeed: Goal = (s) => new SCons(s, null);

export const fail: Goal = (_s) => null;

// `==' in mk.rkt; `==' is not an operator that can be defined here.
export function eq(u: Term, v: Term): Goal {
  return (s) =>
    delay(() => {
      const s2 = unify(u, v, s);
      return s2 === false ? fail(s) : succeed(s2);
    });
}

// `(exist (x ...) g0 g ...)' is `exist((x, ...) => [g0, g, ...])'.  The
// variables are made inside the suspension, so every entry into the
// goal gets fresh ones.
export function exist(f: (...xs: Term[]) => Goal[]): Goal {
  const names = paramNames(f);
  return (s) =>
    delay(() => {
      const xs = names.map((n) => new Var(n));
      return bindStar(succeed(s), ...f(...xs));
    });
}

export function conde(...cs: Goal[][]): Goal {
  return (s) =>
    delay(() => mplusStar(...cs.map((gs) => bindStar(succeed(s), ...gs))));
}

export function trace(msg: string, ...vs: Term[]): Goal {
  return (s) => {
    for (const v of vs) console.log(`${msg}${show(reify(v, s))}`);
    return succeed(s);
  };
}

//----------------------- top level -----------------------

// Iterative, unlike the Racket `take': JavaScript has no tail calls,
// and forcing a long stream would otherwise grow the stack.
export function take<A>(n: number, v: Stream<A>): A[] {
  const out: A[] = [];
  while (out.length < n) {
    if (v === null) break;
    if (v instanceof Thunk) {
      v = force(v);
      continue;
    }
    out.push(v.head);
    v = v.tail;
  }
  return out;
}

// `q' is bound outside the goal so that the answers can be reified
// after they are taken from the stream: the stream a goal builds is a
// `Stream<S>', so reification happens on the way out rather than in it.
export function run(n: number, f: (q: Term) => Goal[]): Term[] {
  const q = new Var(paramNames(f)[0] ?? "q");
  const v = delay(() => bindStar(succeed(emptyS), ...f(q)));
  return take(n, v).map((s) => reify(q, s));
}

export function runAll(f: (q: Term) => Goal[]): Term[] {
  return run(Infinity, f);
}

//------------------------- terms --------------------------

export function sym(s: string): symbol {
  return Symbol.for(s);
}

export const nil: Term = null;

export function cons(a: Term, d: Term): Pair {
  return new Pair(a, d);
}

export function list(...xs: Term[]): Term {
  return xs.reduceRight<Term>((d, a) => new Pair(a, d), nil);
}

export function show(v: Term): string {
  if (v instanceof Var) return `#(${v.name})`;
  if (v instanceof Pair) return `(${showTail(v)})`;
  if (v === null) return "()";
  switch (typeof v) {
    case "symbol":
      return v.description ?? "";
    case "string":
      return JSON.stringify(v);
    case "boolean":
      return v ? "#t" : "#f";
    default:
      return String(v);
  }
}

function showTail(v: Pair): string {
  const a = show(v.car);
  const d = v.cdr;
  if (d === null) return a;
  if (d instanceof Pair) return `${a} ${showTail(d)}`;
  return `${a} . ${show(d)}`;
}

// The source names of a closure's parameters, for display only.  Any
// shape the reader below does not understand (destructuring, defaults,
// a minified closure) falls back to positional names.
function paramNames(f: Function): string[] {
  const src = f.toString();
  const bare = /^\s*(?:async\s+)?([A-Za-z_$][\w$]*)\s*=>/.exec(src);
  const names = bare
    ? [bare[1]]
    : parenthesised(src)
        .split(",")
        .map((p) => p.trim())
        .filter((p) => p !== "");
  const ok =
    names.length === f.length && names.every((p) => /^[A-Za-z_$][\w$]*$/.test(p));
  return ok ? names : Array.from({ length: f.length }, (_, i) => `x${i}`);
}

function parenthesised(src: string): string {
  const open = src.indexOf("(");
  if (open < 0) return "";
  let depth = 0;
  for (let i = open; i < src.length; i++) {
    if (src[i] === "(") depth++;
    else if (src[i] === ")" && --depth === 0) return src.slice(open + 1, i);
  }
  return "";
}
