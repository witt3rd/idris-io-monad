# What is the IO Monad (in Idris)?

Based on Tsoding's Haskell tutorial [What is IO monad?](https://www.ibtimes.com/what-blue-ammonia-saudi-arabia-makes-maiden-shipment-fuel-japan-3052872).

## What is pure functional programming?

To understand why the IO monad is needed, it is first necessary to understand what motivates it: *pure functions*.

To understand pure functions, we can contrast this style of programming to *procedural programming*.

A procedural program is made from composing procedures, e.g.:

```
proc() {
  proc1();
  proc2();
  proc3();
}
```

Inside a procedure, you invoke other procedures sequentially, which can perform *side-effects*, such as performing input/output, changing shared state, etc.  It is considered an *imperative* approach to programming, where we say what to do and when to do it.

Pure functional programs, in contrast, is the composition of a program through pure functions, e.g.:

```
f1(f2(f3(...)))
```

Crucially, a pure function does **not** perform side-effects and always returns the same output given the same input (i.e., *referential transparency*).  In contrast to the imperative approach, it is considered a *declarative* approach to programming.

So, how useful is a program that does not produce side-effects?  Isn't that why we write software?  To take input, produce output, to manipulate state, etc.?  Enter **Monads**.

## The IO Monad

`IO` can be thought of as a *container* that *wraps* a value of a particular type:

```idris
IO : (res : Type) -> Type
```

Let's define a function, `whatIsYourName`, that is of type `IO ()`.  We can use `do` notation to provide syntactic sugar for writing imperative-like programs (see Chapter 5 of [Type-Driven Development with Idris](https://www.manning.com/books/type-driven-development-with-idris)).

```idris
whatIsYourName : IO ()
whatIsYourName = do
  putStrLn "What is your name?"
  name <- getLine
  putStrLn ("Hello " ++ name)
```

```
*src/Main> :exec whatIsYourName
What is your name?
Donald
Hello Donald
```

What is this doing?  How can a pure functional program interact with the outside world like this?

## Pure Functional World

What is a side-effect *really*?  It is something that modifies the *world*.  What if we made this explicit?  Let's define a data type that contains the entire state of the world - everything, including all the particles.  And let's define a function that takes the current state of the world, modifies it in some way, and returns it:

```idris
data Wrld = TheWrld

f : Wrld -> Wrld
```

Note: We are using `Wrld` instead of `World`, since Idris actually defines `World` in prelude as part of `IO`.

This is a pure function: it takes a world and gives a world.  Any action it performs is *contained* within the world state.  Whatever the original state of the world, it will modify it the same way.  For example:

```idris
printStr : String -> Wrld -> Wrld
printStr str world = ?printStr_rhs

readStr : Wrld -> (String, Wrld)
readStr world = ?readStr_rhs
```

The `printStr` pure function will, given a `String` and `Wrld`, return `Wrld` in which the string has been printed.  The `readStr` function will, given `Wrld`, return a pair of the string that was read along with the new state of the world.  In both cases, the same results are produced given the same initial conditions.  (We leave these unimplemented for now.)

We can rewrite our original `whatIsYourName` function using these functions:

```idris
whatIsYourPureName : Wrld -> Wrld
whatIsYourPureName w1 = w4
  where
    w2 : Wrld
    w2 = printStr "What is your name?" w1

    stringWorld : (String, Wrld)
    stringWorld = readStr w2

    w4 : Wrld
    w4 = printStr ("Hello " ++ (fst stringWorld)) (snd stringWorld)
```

This function is implemented using a `where` block that defines a set of intermediate results, each the result of a pure function.  Notice there is **no explicit sequence** of operations.  The main function simply returns the final state of the world, `w4`, and the program *follows* the chain of dependencies necessary to produce it:  `w4` depends on `stringWorld`, which depends on `w2`, which depend on `w1`, which is the input to the main function.

The main point of this example is to illustrate how it is possible to achieve imperative-like, side-effecting programs using pure, declarative functions by keeping track of the modifications to "the world" state.

## Branching the World

In the multiverse hypothesis, every possible path through every alternative is simultaneously taken.  We can achieve something similar by having a function that *branches* the world, such as:

```idris
branch : Wrld -> (Wrld, Wrld)
branch w = (printStr "I love you!" w,
            printStr "I hate you!" w)
```

For pure functional programs, this is a bad thing.  We do not want multiple versions of the world to exist. As is, there is nothing preventing the same world state (`w` in this example) from being used twice.  There are several solutions to this.

### Uniqueness Typing

Some programming languages, like [Clean](https://clean.cs.ru.nl/Clean) and [Idris](http://docs.idris-lang.org/en/latest/reference/uniqueness-types.html), support [uniqueness types](https://en.wikipedia.org/wiki/Uniqueness_type), which is a guarantee that the compiler makes that an object is only referenced once.  It also enables the value to be updated in place, saving memory and increasing performance (less garbage collection).

In Idris, we must use a language extension to enable uniqueness types:

```idris
%language UniquenessTypes
```

We can then define a unique type based on our world state:

```idris
data UWrld : Wrld -> UniqueType where
  MkUW : UWrld w
```

**TODO: implement `whatIsYourUniqueName`**

### Hiding the World

Alternatively, we can "hide" the world by introducing a *transformer*:

```idris
WrldT : (a : Type) -> Type
WrldT a = Wrld -> (a, Wrld)
```

```idris
readStrT : WrldT String
readStrT = readStr

printStrT : String -> WrldT ()
printStrT s w = ((), printStr s w)
```

But, how do we compose these transformer functions?  First, let's understand currying and uncurrying of functions.

#### Currying and Uncurrying

Consider a simple addition function that takes two integers and returns their sum:
```idris
f : Integer -> Integer -> Integer
f x y = x + y
```

We can invoke it normally, such as:
```
*src/Main> f 10 20
30 : Integer
```

Pure functional languages like Idris and Haskell are based on the lambda calculus, which defines function application on single arguments.  It is actually syntactic sugar that allows us to define higher *arity* functions.

We can explicitly define a a function that has the same signature (parenthesis added for emphasis, but they are irrelevant), but takes a single argument `x` and returns a lambda (anonymous) function that takes a single argument `y` and performs the sum:
```idris
g : Integer -> (Integer -> Integer)
g x = \y => x + y
```

This can be explicitly invoked as:
```
*src/Main> g 10
\y => prim__addBigInt 10 y : Integer -> Integer
```
which demonstrates, albeit a bit ugly, that it returns the lambda, which can be further invoked:

```
*src/Main> (g 10) 20
30 : Integer
```
More concisely:
```
*src/Main> g 10 20
30 : Integer
```
But this is actually how the original function works _implicitly_:
```
*src/Main> f 10
f 10 : Integer -> Integer
```
The process can be reversed by un-currying.  We define a function that takes the curried function `f` and returns a lambda that takes a pair of arguments and returns the result of applying the original function:

```idris
uncurry : (Integer -> Integer -> Integer) -> ((Integer, Integer) -> Integer)
uncurry f = \(a,b) => f a b
```

```
*src/Main> Main.uncurry f (10, 20)
30 : Integer
```
Not the use of the `Main.` disambiguator, because `uncurry` is built-in:
```
*src/Main> :t uncurry
uncurry : (a -> b -> c) -> (a, b) -> c

*src/Main> uncurry f (10, 20)
30 : Integer
```

#### Composing transformers

We can make a custom operator that will allow us to easily compose multiple transformer operations together.  Note that our definition of `WrldT a` is a *type synonym* for `Wrld -> (a, Wrld)`, which means that we can imagine substituting the expansion, which I've given as comments at the end of each line of the type signature:

```idris
infixl 1 >>>=
(>>>=) : WrldT a          -- Wrld -> (a, Wrld)
      -> (a -> WrldT b)   -- (a -> Wrld -> (b, Wrld))
      -> WrldT b          -- Wrld -> (b, Wrld)
```

Thus, fully expanded, we have:
```idris
Wrld -> (a, Wrld) -> (a -> Wrld -> (b, Wrld)) -> Wrld -> (b, Wrld)
```

The first argument, which we'll call `wt`, is the result of a world transform, which is a function from `Wrld` to `(a, Wrld)`:
```idris
wt : Wrld -> (a, Wrld)
```

The second argument, which we'll call `f`, is a function:
```idris
f : a -> Wrld -> (b, Wrld)
```

Recalling the type signature of `uncurry : (a -> b -> c) -> (a, b) -> c`, we can recognized `f` can be uncurried:
```idris
uncurry f : (a, Wrld) -> (b, Wrld)
```
where the first argument is the output of `wt` and the output is our desired output of the composition.  Thus, the implementation of `>>>=` is
```idris
wt >>>= f = uncurry f . wt
```

We can now reimplement the program using transformers and transformer composition, we have:
```idris
whatIsYourPureNameT : WrldT ()
whatIsYourPureNameT =
  printStrT "What is your name?" >>>= \_ =>
  readStrT                       >>>= \name =>
  printStrT ("Hello " ++ name)
```
Here, the implementation of WrldT and any manipulation of Wrld is completely hidden.

And this is essentially the IO Monad.

## `do` Notation

In order to use the syntactic sugar of `do` notation, we only need to prove to the type system that `WrldT` is a monad.  To qualify, we must implement the `Monad` interface.

Since we used a type synonym to define `WrldT`, we cannot define an interface instance for it.  So, let's create a wrapper type:

```idris
-- newtype WorldM a = WorldM { asT :: WorldT a }
data WrldM : a -> Type where
  MkWrldM : (asT : WrldT a) -> WrldM asT
```

```idris
(>>=) : Monad m => m a -> (a -> m b) -> m b -- also called "bind"
join  : Monad m => m (m a) -> m a           -- also called "flatten"
```
There is a type constraint on `Monad` being an `Applicative`:
```idris
pure  : Applicative f => a -> f a
(<*>) : Applicative f => f (a -> b) -> f a -> f b
```
And an `Applicative` is also a `Functor`:
```idris
 map : Functor f => (func : a -> b) -> f a -> f b
```

```Idris
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
```

We now need to make wrappers for our IO functions:

```idris
printStrM : String -> WrldM ()
printStrM = ?printStrM -- WorldM . printStrT

readStrM : WrldM String
readStrM = ?readStrM -- WrldM readStrT
```

And, finally, we can rewrite our main program using `do` notation:
```idris
whatIsYourPureNameM : WrldM ()
whatIsYourPureNameM = do
  printStrM "What is your name?"
  name <- readStrM
  printStrM ("Hello " ++ name)
```

To run it, however, requires unwrapping it and passing the initial world state:

```
-- asT whatIsYourPureNameM World
*src/Main>
```

## IO is Unsafe

```haskell
import System.IO.Unsafe

data World = World deriving Show

printStr :: String -> World -> World
printStr s !w = unsafePerformIO (putStrLn s >> return w)

readStr :: World -> (String, World)
readStr !w = unsafePerformIO (getLine >>= (\s -> return (s, w)))
```
