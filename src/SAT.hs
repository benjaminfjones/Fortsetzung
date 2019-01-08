{-# LANGUAGE InstanceSigs #-}

module SAT
  (
    -- * Problem specification
    Expr

    -- * SAT solver
  , runSat

    -- * Examples
  , p1
  , p2
  , p3
  , p4
  )
where

import Control.Monad (when)
import Control.Monad.Trans.Class
import Data.IORef
import Data.List (foldl')
import Data.Maybe (fromMaybe)

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified System.Exit as E


-- | The continuation monad.
--
--   'r' is the result type
--   'a' is the type of the intermediate value this continuation produces
--
--   (a -> r) is like the finalizer (or it completes the computation that
--   produces an 'a')
--
--   a value of type 'Cont r a' is a function that takes a finalizer, does
--   something producing a value of type 'a' and then runs the finalizer on it
--   to produce a value of type 'r'.
--
--   The "finalizer" need not be the last thing evaluated by the 'Cont r a'
--   but the return type 'r' must be the same.
--
newtype Cont r a = Cont { runCont :: (a -> r) -> r }

instance Functor (Cont r) where
  fmap :: (a -> b) -> Cont r a -> Cont r b
  g `fmap` Cont c = Cont (\f -> c (f . g))

instance Applicative (Cont r) where
  pure :: a -> Cont r a
  pure x = Cont (\f -> f x)

  -- splat runs the RHS continuation producing an intermediate of type 'a',
  -- then passes that to the LHS whose intermediate is 'a -> b' which consumes
  -- the 'a' and leaves a 'b' to be finalized, giving a 'Cont r b'
  (<*>) :: Cont r (a -> b) -> Cont r a -> Cont r b
  Cont g <*> Cont c = Cont (\f -> c (\va -> g (\atb -> f (atb va))))
  -- c :: (a -> r) -> r
  -- f :: (b -> r) -> r
  -- g :: ((a -> b) -> r) -> r

instance Monad (Cont r) where
  -- bind runs the LHS continuation partially filling the (a -> r) hole with a
  -- new hole @\va -> (runCont (fab va)) f@ that takes a (b -> r) and supplies
  -- it to the RHS applied to the intermediate 'a'.
  (>>=) :: Cont r a -> (a -> Cont r b) -> Cont r b
  Cont c >>= fab = Cont (\f -> c (\va -> (runCont (fab va)) f))


-- Simple Experiments ----------------------------------------------------------

double :: Int -> Cont Int Int
double x = Cont (\f -> f (2*x))

inc :: Int -> Cont Int Int
inc x = Cont (\f -> f (x+1))

-- | Double and increment an int
--
-- ghci> runCont (doubleAndInc 5) id
-- 11
--
doubleAndInc :: Int -> Cont Int Int
doubleAndInc x = do
  y <- double x
  inc y


-- callCC ----------------------------------------------------------------------

-- | Call with current continuation
--
-- k :: a -> r
-- f :: (a -> Cont r b) -> Cont r a
--
callCC :: ((a -> Cont r b) -> Cont r a) -> Cont r a
callCC f = Cont $ \k -> runCont (f (shortCut k)) k
  where
  -- shortCut :: (a -> r) -> (a -> Cont r b)
  shortCut k = \a -> Cont $ \_ -> k a


-- Backtracking ----------------------------------------------------------------
--
-- A naive backtracking SAT solver implemented using 'callCC' and a stack of
-- continuations held in an IORef.
--

-- | A monad transformer version of `Cont`
newtype ContT r m a = ContT { runContT :: (a -> m r) -> m r }

-- | A monad transformer version of `callCC`
callCCT :: ((a -> ContT r m b) -> ContT r m a) -> ContT r m a
callCCT f = ContT (\k -> runContT (f (\a -> ContT $ \_ -> (k a))) k)

instance Functor (ContT r m) where
  fmap f (ContT c) = ContT (\k -> c (k . f))

instance Applicative (ContT r m) where
  pure a = ContT ($ a)
  ContT g <*> ContT c = ContT $ \k -> g (\f -> c (\a -> k (f a)))

instance Monad (ContT r m) where
  ContT ca >>= f = ContT $ \k -> ca (\a -> runContT (f a) k)

instance MonadTrans (ContT r) where
  lift ma = ContT (\k -> ma >>= k)


-- | Symbolic boolean expressions
data Expr
  = Var String       -- ^ boolean variable
  | Lit Bool         -- ^ boolean literal
  | Not Expr         -- ^ negation
  | And Expr Expr    -- ^ AND
  | Or Expr Expr     -- ^ OR
  | Impl Expr Expr   -- ^ Implication
  | Iff Expr Expr    -- ^ IF
  deriving (Eq, Show)

-- | An evaluation environment mapping variable names to expressions
type Environment = Map String Expr

-- | Reduces a boolean expression to a normal form given a partial mapping of
-- variable names to sub-expressions. Some simplifications are done along the
-- way.
eval :: Environment -> Expr -> Expr
eval env expr =
  case expr of
    Var name -> fromMaybe (Var name) (Map.lookup name env)

    v@(Lit _) -> v

    Not x -> case eval env x of
               Lit b -> Lit (not b)
               Not y -> y
               y -> Not y

    And x y ->
      case (eval env x, eval env y) of
        (Lit False, _) -> Lit False
        (_, Lit False) -> Lit False
        (Lit True, y') -> y'
        (x', Lit True) -> x'
        (x', y')       -> And x' y'

    Or x y ->
      case (eval env x, eval env y) of
        (Lit True, _)   -> Lit True
        (Lit False, y') -> y'
        (_, Lit True)   -> Lit True
        (x', Lit False) -> x'
                           -- -P v P is equiv. to True
                           --
                           -- Because of this simplification a variable may
                           -- not appear in a valid result environment. This
                           -- means the variable is unbound.
        (x', y')        -> if x' == eval env (Not y')
                             then Lit True
                             else Or x' y'

    Impl x y -> eval env (Or (Not x) y)

    Iff x y -> eval env (Or (And x y) (And (Not x) (Not y)))


-- | SAT solver using exhaustive backtracking search.
--
-- Returns `Nothing` if the expression is not satisfiable. If the epxression is
-- satisfiable, returns `Just mapping` with a valid variable mapping.
--
sat :: Expr -> ContT r IO (Maybe Environment)
sat expr = do
  -- A new (empty) stack of continuations
  contStack <- lift (newIORef [])

  callCCT $ \exit -> do
    let expr0 = eval Map.empty expr
    res <- go expr0 True contStack exit
    case res of
      -- failure: backtrack and try again
      Nothing -> backtrack contStack exit
      -- possible solution: check and backtrack if it doesn't satisfy expr0
      Just vars -> case eval vars expr0 of
        Lit True -> exit res
        _        -> backtrack contStack exit

  where

    -- try to pop a continuation off the stack and enter it
    backtrack contStack exit = do
      next <- lift (readIORef contStack)
      lift $ putStrLn ("backtracking ... depth = " ++ show (length next))
      case next of
        []        -> exit Nothing
        next:rest -> do lift (writeIORef contStack rest)
                        next

    -- 'go' examines the given expression and attempts to return an
    -- environment in which the expression evaluates to True.
    --
    -- For some types of expressions it will make an arbitrary choice and push
    -- onto the continuation stack the opposite choice (to be explored later
    -- after backtracking).
    --
    -- The 'polarity' parameter tells us whether to try to make 'expr' True or
    -- False. This is useful when recursively finding an assignment for
    -- expressions like @Not x@. We use the value of polarity in this case to
    -- choose @Lit False@ for @x@ first.
    --
    go expr polarity contStack exit = case expr of

      -- we choose 'Lit polarity' here for the variable and the opposite
      -- choice is pushed on the stack
      Var name -> do
        res <- callCCT $ \k -> do
          lift (modifyIORef contStack (k (Lit (not polarity)) :))
          pure (Lit polarity)
        pure $ Just (Map.singleton name res)

      Lit b -> pure (if (b == polarity) then Just Map.empty else Nothing)

      -- we choose to try and find an assignment that satisfies the LHS first
      -- and push trying the RHS on the stack
      Or a b -> do
        side <- callCCT $ \k -> do
          lift (modifyIORef contStack (k b :))
          pure a
        go side polarity contStack exit

      And a b -> do
        ares <- go a polarity contStack exit
        bres <- go b polarity contStack exit
        -- note: ares and bres could have conflicting assignments here. If
        -- there is a satisfying solution then we are gauranteed to find it
        -- and in such a case ares and bres will be consistent (modulo clauses
        -- in which a literal and its negation appear).
        pure (Map.union <$> ares <*> bres)

      Not a -> go a (not polarity) contStack exit

      -- other forms can be immediately reduced
      _ -> go (eval Map.empty expr) polarity contStack exit


runSat :: Expr -> IO ()
runSat expr = runContT (sat expr) exitRes

exitRes :: Maybe Environment -> IO ()
exitRes env = case env of
                Nothing  -> E.exitWith (E.ExitFailure 1)
                Just env -> do putStrLn "SAT"
                               print env
                               E.exitSuccess

-- Examples -----

p1 :: Expr
p1 = And (Var "x") (Not (Var "y"))

p2 :: Expr
p2 = Impl (Var "x") (Or (Var "y") (Not (Var "y")))

-- | A Horn formula
p3 :: Expr
p3 = And d (And (Var "a") (Var "b"))
  where
  d = Or (Var "c") (Or (Not (Var "a")) (Not (Var "b")))

-- | UNSAT, 8-clause 3-CNF in 3 vars
--
-- TODO: causes extreme backtracking!
p4 :: Expr
p4 = foldl' (\f c -> And f c) (Lit True) cs
  where
  cs = [ or3 (f p1 "x") (f p2 "y") (f p3 "z") | p1 <- [True,False]
                                              , p2 <- [True,False]
                                              , p3 <- [True,False] ]
  f p name = if p then Var name else Not (Var name)
  or3 a b c = Or a (Or b c)
