-- | A Haskell version of mk.rkt.
--
-- The structure follows the Racket source section by section.  Three
-- places had to be adapted rather than transliterated:
--
--   * Racket distinguishes fresh logic variables by @eq?@ (struct
--     identity).  Haskell has no such notion, so a variable carries an
--     integer and goals thread a counter alongside the substitution.
--
--   * @delay@/@force@ are kept explicit even though Haskell is lazy: the
--     interleaving in 'mplus' works by /observing/ that a stream is
--     suspended, which a transparent thunk would not allow.
--
--   * @name-prefix@ was a mutable global set by @set-name-prefix@; here
--     it is a parameter of 'reifyWith' ('reify' uses the default \"_\").
--     @display-code@/@debug-display@ printed the source of a @run@ form,
--     which is not available without macros, and is dropped.
module MK where

import qualified Debug.Trace as Debug


--------------------- substitution ----------------------

newtype Var = Var Int
  deriving (Eq)

data Term
  = TVar Var
  | TSym String
  | TStr String
  | TNum Integer
  | TBool Bool
  | TNil
  | TPair Term Term
  deriving (Eq)

type S = [(Var, Term)]

emptyS :: S
emptyS = []

sizeS :: S -> Int
sizeS = length

extS :: Var -> Term -> S -> S
extS x v s = (x, v) : s

walk :: Term -> S -> Term
walk v s =
  case v of
    TVar x ->
      case lookup x s of
        Nothing -> v
        Just p  -> walk p s
    _ -> v

walkStar :: Term -> S -> Term
walkStar v s =
  case walk v s of
    TVar x      -> TVar x
    TPair a d   -> TPair (walkStar a s) (walkStar d s)
    v'          -> v'

unify :: Term -> Term -> S -> Maybe S
unify u v s =
  case (walk u s, walk v s) of
    (TVar x, TVar y) | x == y -> Just s
    (TVar x, v')              -> Just (extS x v' s)
    (u', TVar y)              -> Just (extS y u' s)
    (TPair a d, TPair a' d')  -> unify a a' s >>= unify d d'
    (u', v') | u' == v'       -> Just s
             | otherwise      -> Nothing

namePrefix :: String
namePrefix = "_"

name :: String -> Int -> Term
name prefix n = TSym (prefix ++ show n)

reifyS :: String -> Term -> S -> S
reifyS prefix v s =
  case walk v s of
    TVar x    -> extS x (name prefix (sizeS s)) s
    TPair a d -> reifyS prefix d (reifyS prefix a s)
    _         -> s

reifyWith :: String -> Term -> S -> Term
reifyWith prefix v s =
  let v' = walkStar v s
  in walkStar v' (reifyS prefix v' emptyS)

reify :: Term -> S -> Term
reify = reifyWith namePrefix


---------------------- composition ----------------------

-- | A goal runs against a substitution paired with the counter that
-- supplies fresh variables.
data State = State { subst :: S, counter :: Int }

-- | A goal maps a state to a stream of states: 'Stream' instantiated at
-- the substitution it threads.
type Goal = State -> Stream State

-- | The stream is parameterised by what it carries.  @Delay@ is
-- @thunk@: its field is lazy, so the suspension is real, but the
-- constructor keeps it visible to 'mplus' and 'bind'.
data Stream a
  = Empty
  | Delay (Stream a)
  | Cons a (Stream a)

force :: Stream a -> Stream a
force (Delay s) = s
force s         = s

bind :: (a -> Stream b) -> Stream a -> Stream b
bind g v =
  case v of
    Empty      -> Empty
    Delay _    -> Delay (bind g (force v))
    Cons hd tl -> mplus (g hd) (Delay (bind g tl))

-- | @bind*@: the goals are applied left to right.
bindStar :: Stream State -> [Goal] -> Stream State
bindStar v []       = v
bindStar v (g : gs) = bindStar (bind g v) gs

mplus :: Stream a -> Stream a -> Stream a
mplus v f =
  case v of
    Empty      -> f
    Delay _    -> Delay (mplus f (force v))
    Cons hd tl -> Cons hd (Delay (mplus f tl))

mplusStar :: [Stream a] -> Stream a
mplusStar []       = Empty
mplusStar [e]      = e
mplusStar (e : es) = mplus e (Delay (mplusStar es))


------------------- goal constructors -------------------

succeed :: Goal
succeed st = Cons st Empty

-- | @fail@ in mk.rkt; renamed to avoid the clash with 'Prelude.fail'.
failure :: Goal
failure _ = Empty

infix 4 ===

(===) :: Term -> Term -> Goal
(===) u v st =
  Delay
    (case unify u v (subst st) of
       Just s  -> succeed st { subst = s }
       Nothing -> failure st)

-- | Conjunction, the implicit @g0 g ...@ of @exist@ and of a @conde@
-- clause.  Like @bind*@ it inserts no delay of its own.
conj :: [Goal] -> Goal
conj gs st = bindStar (succeed st) gs

-- | The variables of @(exist (x ...) ...)@: 'Term' for one, a tuple of
-- 'Term's for several.
class Fresh a where
  freshVars :: Int -> (a, Int)

instance Fresh Term where
  freshVars n = (TVar (Var n), n + 1)

instance (Fresh a, Fresh b) => Fresh (a, b) where
  freshVars n0 =
    let (a, n1) = freshVars n0
        (b, n2) = freshVars n1
    in ((a, b), n2)

instance (Fresh a, Fresh b, Fresh c) => Fresh (a, b, c) where
  freshVars n0 =
    let (a, n1) = freshVars n0
        (b, n2) = freshVars n1
        (c, n3) = freshVars n2
    in ((a, b, c), n3)

instance (Fresh a, Fresh b, Fresh c, Fresh d) => Fresh (a, b, c, d) where
  freshVars n0 =
    let (a, n1) = freshVars n0
        (b, n2) = freshVars n1
        (c, n3) = freshVars n2
        (d, n4) = freshVars n3
    in ((a, b, c, d), n4)

instance (Fresh a, Fresh b, Fresh c, Fresh d, Fresh e)
      => Fresh (a, b, c, d, e) where
  freshVars n0 =
    let (a, n1) = freshVars n0
        (b, n2) = freshVars n1
        (c, n3) = freshVars n2
        (d, n4) = freshVars n3
        (e, n5) = freshVars n4
    in ((a, b, c, d, e), n5)

-- | @(exist (x ...) g0 g ...)@ is @exist $ \(x, ...) -> [g0, g ...]@.
exist :: Fresh a => (a -> [Goal]) -> Goal
exist f st =
  Delay
    (let (xs, n) = freshVars (counter st)
     in bindStar (succeed st { counter = n }) (f xs))

conde :: [[Goal]] -> Goal
conde cs st =
  Delay (mplusStar [bindStar (succeed st) gs | gs <- cs])

-- | @trace@ in mk.rkt; the variables' source names are not available, so
-- the reified terms are printed under the message alone.
traceG :: String -> [Term] -> Goal
traceG msg vs st =
  Debug.trace
    (unlines [msg ++ show (reify v (subst st)) | v <- vs])
    (succeed st)


----------------------- top level ------------------------

-- | The @take@ of mk.rkt is @take n . streamToList@: laziness makes the
-- bound unnecessary here, and @run*@ needs no infinity.
streamToList :: Stream a -> [a]
streamToList v =
  case v of
    Empty      -> []
    Delay _    -> streamToList (force v)
    Cons hd tl -> hd : streamToList tl

-- | @q@ is bound outside the goal so that the answers can be reified
-- after they are taken from the stream: the stream here is a @Stream
-- State@, so reification happens on the way out rather than inside it.
runAll :: (Term -> [Goal]) -> [Term]
runAll f =
  let q  = TVar (Var 0)
      st = State { subst = emptyS, counter = 1 }
  in map (reify q . subst) (streamToList (Delay (bindStar (succeed st) (f q))))

run :: Int -> (Term -> [Goal]) -> [Term]
run n f = take n (runAll f)


------------------------- terms --------------------------

sym :: String -> Term
sym = TSym

str :: String -> Term
str = TStr

num :: Integer -> Term
num = TNum

bool :: Bool -> Term
bool = TBool

nil :: Term
nil = TNil

infixr 5 `cons`

cons :: Term -> Term -> Term
cons = TPair

list :: [Term] -> Term
list = foldr TPair TNil

instance Show Var where
  show (Var n) = "_." ++ show n

instance Show Term where
  show v =
    case v of
      TVar x       -> show x
      TSym s       -> s
      TStr s       -> show s
      TNum n       -> show n
      TBool True   -> "#t"
      TBool False  -> "#f"
      TNil         -> "()"
      TPair _ _    -> "(" ++ showTail v ++ ")"
    where
      showTail (TPair a d) =
        case d of
          TNil      -> show a
          TPair _ _ -> show a ++ " " ++ showTail d
          _         -> show a ++ " . " ++ show d
      showTail t = show t
