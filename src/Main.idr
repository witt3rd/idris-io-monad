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
WrldT x = Wrld -> (x, Wrld)

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
data WrldM : (a : Type) -> Type where
  MkWrldM : (asT : WrldT a) -> WrldM a

myWrldM : WrldM String
myWrldM = MkWrldM (\w => ("hello", w))

data ListOf : a -> Type where
  MkListOf : (list : List a) -> ListOf a

myStrLst : ListOf String
myStrLst = MkListOf ["hello"]

Functor WrldM where
  -- map : (func : a -> b) -> f a -> f b
  map f (MkWrldM asT) = MkWrldM $ (\(a, w) => (f a, w)) . asT

Applicative WrldM where
  -- pure : a -> f a
  pure x = MkWrldM (\w => (x, w))

  -- (<*>) : f (a -> b) -> f a -> f b
  (MkWrldM wtf) <*> (MkWrldM wt) = MkWrldM (wtf >>>= \f =>
                                            wt  >>>= \x =>
                                            \w    => (f x, w))
      -- MkWrldM ( \ w =>
      --   let (f,w1) = wtf w
      --       (a,w2) = wt w1
      --   in  (f a, w2)
      -- )

Monad WrldM where
  -- (>>=) : m a -> (a -> m b) -> m b
  -- wt >>= f = WorldM (asT wt >>>= asT . f)
  (MkWrldM wt) >>= f = MkWrldM ( \ w =>
      let (x,w1) = wt w
          MkWrldM foo = f x
          (y,b) = foo w1
      in  (y,b)
    )

printStrM : String -> WrldM ()
printStrM = MkWrldM . printStrT

readStrM : WrldM String
readStrM = MkWrldM readStrT

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
