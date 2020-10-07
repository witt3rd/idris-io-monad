module Main

%language UniquenessTypes

{-
 - IO monad
 -}
whatIsYourName : IO ()
whatIsYourName = do
  putStrLn "What is your name?"
  name <- getLine
  putStrLn ("Hello " ++ name)

{-
 - The World
 -}
data Wrld = TheWrld

printStr : String -> Wrld -> Wrld
printStr str world = ?printStr_rhs

readStr : Wrld -> (String, Wrld)
readStr world = ?readStr_rhs


whatIsYourPureName : Wrld -> Wrld
whatIsYourPureName w1 = w4
  where
    w2 : Wrld
    w2 = printStr "What is your name?" w1

    stringWorld : (String, Wrld)
    stringWorld = readStr w2

    w4 : Wrld
    w4 = printStr ("Hello " ++ (fst stringWorld)) (snd stringWorld)


{-
 - Branching the world
 -}
branch : Wrld -> (Wrld, Wrld)
branch w = (printStr "I love you!" w,
            printStr "I hate you!" w)

{-
 - Uniqueness types
 -}
data UWrld : Wrld -> UniqueType where
   MkUWrld : UWrld w

-- printStrU : String -> UWrld TheWrld -> UWrld TheWrld
-- printStrU str world = ?printStrU_rhs
--
-- readStrU : UWrld TheWrld -> (String, (UWrld TheWrld))
-- readStrU world = ?readStrU_rhs
--
-- branchU : UWrld TheWrld -> UWrld TheWrld
-- branchU x = ?branchU_rhs


{-
 - Hiding the world
 -}
WrldT : (a : Type) -> Type
WrldT a = Wrld -> (a, Wrld)

readStrT : WrldT String
readStrT = readStr

printStrT : String -> WrldT ()
printStrT s w = ((), printStr s w)


{-
 - Currying and uncurrying
 -}
f : Integer -> Integer -> Integer
f x y = x + y

g : Integer -> (Integer -> Integer)
g x = \y => x + y

uncurry' : (Integer -> Integer -> Integer) -> ((Integer, Integer) -> Integer)
uncurry' f = \(a,b) => f a b


{-
 - Composing transformers
 -}
infixl 1 >>>=
(>>>=) : WrldT a          -- Wrld -> (a, Wrld)
      -> (a -> WrldT b)   -- (a -> Wrld -> (b, Wrld))
      -> WrldT b          -- Wrld -> (b, Wrld)
wt >>>= f = uncurry f . wt


whatIsYourPureNameT : WrldT ()
whatIsYourPureNameT =
  printStrT "What is your name?" >>>= \_ =>
  readStrT                       >>>= \name =>
  printStrT ("Hello " ++ name)


{-
 - `do` notation
 -}
 -- newtype WorldM a = WorldM { asT :: WorldT a }
data WrldM : a -> Type where
  MkWrldM : (asT : WrldT a) -> WrldM asT

Functor WrldM where
  -- map : (func : a -> b) -> f a -> f b
  map f x = ?map

Applicative WrldM where
  -- pure : a -> f a
  -- pure x = WorldM (\w -> (x, World))
  pure x = ?pure

  -- (<*>) : f (a -> b) -> f a -> f b
  -- wtf <*> wt = WorldM (asT wtf >>>= \f ->
  --                      asT wt  >>>= \x ->
  --                      ast $ pure $ f x)
  wtf <*> wt = ?ap

Monad WrldM where
  -- (>>=) : m a -> (a -> m b) -> m b
  -- wt >>= f = WorldM (asT wt >>>= asT . f)
  wt >>= f = ?bind

  -- join : m (m a) -> m a
  join x = ?join

printStrM : String -> WrldM ()
printStrM = ?printStrM -- WorldM . printStrT

readStrM : WrldM String
readStrM = ?readStrM -- WrldM readStrT

whatIsYourPureNameM : WrldM ()
whatIsYourPureNameM = do
  printStrM "What is your name?"
  name <- readStrM
  printStrM ("Hello " ++ name)

-- asT whatIsYourPureNameM World

{-
import System.IO.Unsafe

data World = World deriving Show

printStr :: String -> World -> World
printStr s !w = unsafePerformIO (putStrLn s >> return w)

readStr :: World -> (String, World)
readStr !w = unsafePerformIO (getLine >>= (\s -> return (s, w)))
-}
