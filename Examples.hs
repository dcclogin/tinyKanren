-- | Examples and tests for "MK", the Haskell tinyKanren.
--
-- Every case states the query, the expected answers as they are
-- printed, and (for the divergent relations) the bound that makes the
-- query finite.  @main@ runs them all and reports.
--
--   ghc -O0 Examples.hs -o examples && ./examples
--   -- or --
--   runghc Examples.hs
module Main (main) where

import Control.Monad (unless)
import System.Exit (exitFailure)

import MK


------------------------- relations ------------------------

nullo :: Term -> Goal
nullo l = l === nil

conso :: Term -> Term -> Term -> Goal
conso a d p = cons a d === p

caro :: Term -> Term -> Goal
caro p a = exist $ \d -> [conso a d p]

cdro :: Term -> Term -> Goal
cdro p d = exist $ \a -> [conso a d p]

appendo :: Term -> Term -> Term -> Goal
appendo l s out =
  conde
    [ [ nullo l, s === out ]
    , [ exist $ \(a, d, res) ->
          [ conso a d l
          , conso a res out
          , appendo d s res
          ]
      ]
    ]

membero :: Term -> Term -> Goal
membero x l =
  exist $ \(a, d) ->
    [ conso a d l
    , conde
        [ [ x === a ]
        , [ membero x d ]
        ]
    ]

reverso :: Term -> Term -> Goal
reverso l out =
  conde
    [ [ nullo l, nullo out ]
    , [ exist $ \(a, d, res) ->
          [ conso a d l
          , reverso d res
          , appendo res (list [a]) out
          ]
      ]
    ]

-- | Unary numbers: @z@, @(s z)@, @(s (s z))@, ...
zero :: Term
zero = sym "z"

succo :: Term -> Term
succo n = list [sym "s", n]

peano :: Int -> Term
peano n = iterate succo zero !! n

pluso :: Term -> Term -> Term -> Goal
pluso n m out =
  conde
    [ [ n === zero, m === out ]
    , [ exist $ \(n', out') ->
          [ n === succo n'
          , out === succo out'
          , pluso n' m out'
          ]
      ]
    ]

-- | The two relations that make interleaving observable: 'alwayso'
-- succeeds infinitely often, 'nevero' never succeeds and never stops.
-- Both are knots tied through 'conde', whose 'Delay' keeps the
-- recursive occurrence unforced.
alwayso :: Goal
alwayso = conde [[succeed], [alwayso]]

nevero :: Goal
nevero = conde [[nevero]]


--------------------------- cases ---------------------------

data Case = Case String [Term] [String]

cases :: [Case]
cases =
  [ ---------------------------------------------------- unification
    Case "q is 5"
      (runAll $ \q -> [q === num 5])
      ["5"]

  , Case "5 is q (symmetric)"
      (runAll $ \q -> [num 5 === q])
      ["5"]

  , Case "no answers"
      (runAll $ \_ -> [failure])
      []

  , Case "succeed leaves q fresh"
      (runAll $ \_ -> [succeed])
      ["_0"]

  , Case "conflicting equations fail"
      (runAll $ \q -> [q === num 5, q === num 6])
      []

  , Case "the same equation twice"
      (runAll $ \q -> [q === num 5, q === num 5])
      ["5"]

  , Case "atoms of every kind"
      (runAll $ \q -> [q === list [sym "a", str "b", num 3, bool True, bool False, nil]])
      ["(a \"b\" 3 #t #f ())"]

  , Case "an improper list"
      (runAll $ \q -> [q === cons (num 1) (num 2)])
      ["(1 . 2)"]

  , Case "structural unification"
      (runAll $ \q -> [exist $ \(x, y) -> [ list [x, num 2] === list [num 1, y]
                                          , q === list [x, y] ]])
      ["(1 2)"]

  , Case "occurs freely: q is bound to a variable, not a value"
      (runAll $ \q -> [exist $ \x -> [q === x]])
      ["_0"]

    ------------------------------------------------------- reify
  , Case "distinct fresh variables get distinct names"
      (runAll $ \q -> [exist $ \(x, y) -> [q === list [x, y]]])
      ["(_0 _1)"]

  , Case "sharing is visible in the reified answer"
      (runAll $ \q -> [exist $ \(x, y) -> [q === list [x, y, x]]])
      ["(_0 _1 _0)"]

  , Case "a variable equated with another is reified once"
      (runAll $ \q -> [exist $ \(x, y) -> [x === y, q === list [x, y]]])
      ["(_0 _0)"]

  , Case "reification walks under pairs"
      (runAll $ \q -> [exist $ \(x, y) -> [q === cons (list [x, num 1]) y]])
      ["((_0 1) . _1)"]

    ------------------------------------------------------- conde
  , Case "three clauses, three answers"
      (runAll $ \q -> [conde [[q === num 1], [q === num 2], [q === num 3]]])
      ["1", "2", "3"]

  , Case "a failing clause is skipped"
      (runAll $ \q -> [conde [[failure], [q === num 2], [failure], [q === num 4]]])
      ["2", "4"]

  , Case "conde is a disjunction of conjunctions"
      (runAll $ \q -> [conde [ [q === num 1, failure]
                             , [q === num 2, succeed] ]])
      ["2"]

    -- The four answers come out in the order the interleaving in
    -- 'mplus' produces them, which is not the clause order.
  , Case "nested conde multiplies the clauses"
      (runAll $ \q -> [exist $ \(x, y) ->
                         [ conde [[x === num 1], [x === num 2]]
                         , conde [[y === sym "a"], [y === sym "b"]]
                         , q === list [x, y] ]])
      ["(1 a)", "(1 b)", "(2 a)", "(2 b)"]

    ------------------------------------------------------- caro/cdro
  , Case "caro of a list"
      (runAll $ \q -> [caro (list [sym "a", sym "b", sym "c"]) q])
      ["a"]

  , Case "cdro of a list"
      (runAll $ \q -> [cdro (list [sym "a", sym "b", sym "c"]) q])
      ["(b c)"]

  , Case "caro run backwards builds a list"
      (runAll $ \q -> [caro q (sym "a"), cdro q (list [sym "b"])])
      ["(a b)"]

    ------------------------------------------------------- appendo
  , Case "appendo forwards"
      (runAll $ \q -> [appendo (list [num 1, num 2]) (list [num 3, num 4]) q])
      ["(1 2 3 4)"]

  , Case "appendo with a fresh tail"
      (runAll $ \q -> [exist $ \x -> [appendo (list [num 1]) x (list [num 1, num 2])
                                     , q === x]])
      ["(2)"]

  , Case "appendo backwards: every split of a three-element list"
      (runAll $ \q -> [exist $ \(x, y) -> [ appendo x y (list [sym "a", sym "b", sym "c"])
                                          , q === list [x, y] ]])
      [ "(() (a b c))"
      , "((a) (b c))"
      , "((a b) (c))"
      , "((a b c) ())"
      ]

  , Case "appendo with both arguments fresh is infinite"
      (run 4 $ \q -> [exist $ \(x, y, z) -> [appendo x y z, q === list [x, y, z]]])
      [ "(() _0 _0)"
      , "((_0) _1 (_0 . _1))"
      , "((_0 _1) _2 (_0 _1 . _2))"
      , "((_0 _1 _2) _3 (_0 _1 _2 . _3))"
      ]

    ------------------------------------------------------- membero
  , Case "membero enumerates the elements"
      (runAll $ \q -> [membero q (list [num 1, num 2, num 3])])
      ["1", "2", "3"]

  , Case "membero as a test: present"
      (runAll $ \q -> [membero (num 2) (list [num 1, num 2, num 3]), q === bool True])
      ["#t"]

  , Case "membero as a test: absent"
      (runAll $ \q -> [membero (num 9) (list [num 1, num 2, num 3]), q === bool True])
      []

  , Case "membero repeats a repeated element"
      (runAll $ \q -> [membero q (list [sym "a", sym "b", sym "a"])])
      ["a", "b", "a"]

  , Case "two memberos intersect"
      (runAll $ \q -> [ membero q (list [num 1, num 2, num 3])
                      , membero q (list [num 3, num 4, num 1]) ])
      ["1", "3"]

  , Case "membero of a fresh list is infinite"
      (run 3 $ \q -> [membero (sym "x") q])
      [ "(x . _0)"
      , "(_0 x . _1)"
      , "(_0 _1 x . _2)"
      ]

    ------------------------------------------------------- reverso
  , Case "reverso forwards"
      (runAll $ \q -> [reverso (list [num 1, num 2, num 3]) q])
      ["(3 2 1)"]

  , Case "reverso backwards"
      (run 1 $ \q -> [reverso q (list [num 1, num 2, num 3])])
      ["(3 2 1)"]

    ------------------------------------------------------- arithmetic
  , Case "2 + 3 = 5"
      (runAll $ \q -> [pluso (peano 2) (peano 3) q])
      ["(s (s (s (s (s z)))))"]

  , Case "5 - 2 = 3 (subtraction is addition backwards)"
      (runAll $ \q -> [pluso (peano 2) q (peano 5)])
      ["(s (s (s z)))"]

  , Case "every pair summing to 3"
      (runAll $ \q -> [exist $ \(x, y) -> [pluso x y (peano 3), q === list [x, y]]])
      [ "(z (s (s (s z))))"
      , "((s z) (s (s z)))"
      , "((s (s z)) (s z))"
      , "((s (s (s z))) z)"
      ]

  , Case "addition with both summands fresh is infinite"
      (run 3 $ \q -> [exist $ \(x, y, z) -> [pluso x y z, q === list [x, y, z]]])
      [ "(z _0 _0)"
      , "((s z) _0 (s _0))"
      , "((s (s z)) _0 (s (s _0)))"
      ]

    ------------------------------------------------------- interleaving
  , Case "run bounds an infinite stream"
      (run 3 $ \q -> [alwayso, q === bool True])
      ["#t", "#t", "#t"]

  , Case "a finite branch is not starved by an infinite one"
      (run 3 $ \q -> [conde [[q === bool True], [alwayso]], q === bool False])
      ["#f", "#f", "#f"]

  , Case "a divergent branch does not hide an answer in another"
      (run 1 $ \q -> [conde [[nevero], [q === sym "found"]]])
      ["found"]

  , Case "a divergent branch on either side"
      (run 1 $ \q -> [conde [[q === sym "found"], [nevero]]])
      ["found"]

  , Case "asking for none of an infinite stream terminates"
      (run 0 $ \_ -> [alwayso])
      []
  ]


--------------------------- runner ---------------------------

main :: IO ()
main = do
  results <- mapM report cases
  putStrLn ""
  let failed = length (filter not results)
  putStrLn (show (length cases - failed) ++ " / " ++ show (length cases) ++ " passed")
  demoTrace
  unless (failed == 0) exitFailure

report :: Case -> IO Bool
report (Case what got want)
  | actual == want = do
      putStrLn ("ok   " ++ what ++ "  =>  " ++ unwords actual)
      return True
  | otherwise = do
      putStrLn ("FAIL " ++ what)
      putStrLn ("       want: " ++ unwords want)
      putStrLn ("       got:  " ++ unwords actual)
      return False
  where actual = map show got

-- | 'traceG' prints through "Debug.Trace", so it is shown rather than
-- checked: the goal itself only succeeds.
demoTrace :: IO ()
demoTrace = do
  putStrLn "\ntraceG:"
  print (runAll $ \q ->
           [ exist $ \(x, y) ->
               [ x === num 1
               , traceG "  x, y = " [x, y]
               , q === list [x, y] ] ])
