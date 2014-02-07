{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable #-}

import Control.Arrow ((***), first, second)
import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Error
import Data.Monoid
import Data.List
import Data.Function
import Data.Typeable

import Test.QuickSpec
import Test.QuickCheck

-- Program representation -------------------------------------------------

newtype Prog = Prog { commands :: [Cmd] }
  deriving (Monoid, Typeable, Show)

data Cmd  = Register Pid Name
          | Unregister Name
          | Spawn Pid
          | Crash | Whereis Name
          | Return (Maybe Pid)
          | Use Pid | Bind Pid
  deriving (Show, Typeable, Eq)

newtype Pid = Pid Int
  deriving (Show, Eq, Ord, Typeable)

data Name = A | B | C | D
  deriving (Show, Eq, Ord, Enum, Bounded, Typeable)

cmd :: Cmd -> Prog
cmd c = Prog [c]

data Vars = Vars { bVars :: [Pid]
                 , fVars :: [Pid] }
  deriving (Typeable, Eq, Ord, Show)

instance Monoid Vars where
  mempty = Vars [] []
  mappend (Vars xs ys) (Vars zs ws) =
    Vars (sort $ union xs zs) (sort $ union ys (ws \\ xs))

progVars :: Prog -> Vars
progVars (Prog cmds)
  | elem Crash cmds = mempty
  | otherwise       = mconcat $ map cmdVars cmds
  where
    cmdVars (Spawn p)      = Vars [p] []
    cmdVars (Bind p)       = Vars [p] []
    cmdVars (Register p _) = Vars [] [p]
    cmdVars (Use p)        = Vars [] [p]
    cmdVars _              = mempty

allThePids :: [Pid]
allThePids = map Pid [0..5]

-- Generators -------------------------------------------------------------

instance Arbitrary Name where
  arbitrary = elements [minBound..maxBound]

instance CoArbitrary Name where
  coarbitrary = coarbitrary . fromEnum

instance Arbitrary Pid where
  arbitrary = elements allThePids

instance Arbitrary Prog where
  arbitrary = sized $ \n -> Prog <$> cmds n []
    where
      cmds n st = frequency [(1, pure []),
                             (n, do c <- cmd st
                                    (c :) <$> cmds (n - 1) (next c st))]
      cmd st =
        oneof $ [ Spawn      <$> elements freshPids | not $ null freshPids ] ++
                [ Register   <$> arbitrary <*> arbitrary
                , Unregister <$> arbitrary
                , Whereis    <$> arbitrary ]
        where
          freshPids = allThePids \\ st

      next (Spawn p)      st = p : st
      next (Register p _) st = p : st
      next Unregister{}   st = st

  shrink (Prog cmds) = map Prog $ shrink cmds

instance Arbitrary Cmd where
  arbitrary = oneof [ Spawn <$> arbitrary
                    , Register <$> arbitrary <*> arbitrary
                    , Unregister <$> arbitrary ]

-- Running programs -------------------------------------------------------

data St = St { pids  :: [Pid]
             , names :: [(Name, Pid)]
             }
  deriving (Eq, Ord, Typeable, Show)

initSt = St [] []

type Run = StateT St (ErrorT String (Writer [Maybe Pid]))

run :: St -> Prog -> (Maybe St, [Maybe Pid])
run st (Prog cmds) = first (either (const Nothing) Just)
                   $ runWriter
                   $ runErrorT
                   $ execStateT (mapM_ runCmd cmds) st

runCmd :: Cmd -> Run ()
runCmd (Spawn p) = do
  guard =<< gets (notElem p . pids)
  modify $ \st -> st { pids = insert p (pids st) }
runCmd (Register p x) = do
  guard =<< gets (elem p . pids)
  modify $ \st ->
    case lookup x (names st) of
      Nothing -> st { names = insert (x, p) $ names st }
      Just{}  -> st
runCmd (Unregister x) = modify $ \st -> st { names = filter ((/= x) . fst) $ names st }
runCmd Crash          = fail ""
runCmd (Whereis x)    = tell . (:[]) =<< gets (lookup x . names)
runCmd (Return m)     = tell [m]
runCmd Use{}          = pure ()
runCmd Bind{}         = pure ()

runInCxt :: Prog -> Prog -> (Maybe St, [Maybe Pid])
runInCxt pre p = run initSt (pre <> p)

genSt :: Vars -> Gen St
genSt (Vars bv fv) = do
  fv' <- sort . (\\ bv) . union fv . nub <$> listOf arbitrary
  -- let fv' = allThePids \\ bv
  St fv' <$> (sort <$> reg fv')
  where
    reg fv' = do
      f <- arbitrary
      return [ (x, p) | x <- [minBound..maxBound], Just p <- [f x], elem p fv' ]

newtype StGen = StGen (Vars -> St)
  deriving (Typeable)

instance Show StGen where
  show _ = "<StGen>"

instance Arbitrary StGen where
  arbitrary = StGen <$> promote genSt

run' :: StGen -> Prog -> (Vars, (Maybe St, [Maybe Pid]))
run' (StGen st) p = (vs, run (st vs) p)
  where vs = progVars p

-- QuickSpec signature ----------------------------------------------------

sig :: [Sig]
sig =
  [ [ "P", "Q", "R" ]  `vars` (undefined :: Prog)
  , [ "Pid1", "Pid2" ] `vars` (undefined :: Pid)
  , [ "X", "Y" ]       `vars` (undefined :: Name)
  -- , [ "A", "B", "C" ]  `vars` (undefined :: Cmd)

  , "_"          `fun0`   ()
  , ", "         `blind2` ((<>) :: Prog -> Prog -> Prog)
  , "spawn"      `blind1` (cmd . Spawn)
  , "register"   `blind2` ((cmd .) . Register)
  , "unregister" `blind1` (cmd . Unregister)
  , "whereis"    `blind1` (cmd . Whereis)
  , "returnNothing" `blind1` (\() -> cmd $ Return Nothing)
  , "returnJust" `blind1` (cmd . Return . Just)
  , "crash"      `blind0` (cmd Crash)
  -- , "0"          `blind0` (mempty :: Prog)
  -- , "1"          `blind1` (\p -> Prog [p])
  -- , "2"          `blind2` (\p q -> Prog [p, q])
  -- , "3"          `blind3` (\p q r -> Prog [p, q, r])
  -- , "spawn"      `blind1` (Spawn)
  -- , "register"   `blind2` (Register)
  -- , "unregister" `blind1` (Unregister)
  -- , "whereis"    `blind1` (Whereis)
  -- , "returnNothing" `blind1` (\() -> Return Nothing)
  -- , "returnJust" `blind1` (Return . Just)
  -- , "crash"      `blind0` Crash

  , observer2 run'
  -- , withTests 5000
  ]

main = quickSpec sig

-- Properties -------------------------------------------------------------

x === y = whenFail (putStrLn $ show x ++ " /= " ++ show y) $ x == y

prop_idem (f, p, q) = run' f (q <> p <> p <> q) === run' f (p <> q <> p <> q)

wth1 = run initSt (Prog [Spawn (Pid 0), Register (Pid 0) A, Register (Pid 0) A, Unregister A])
wth2 = run initSt (Prog [Spawn (Pid 0), Unregister A, Register (Pid 0) A, Register (Pid 0) A])
