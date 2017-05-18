import Data.Vect
--------------------------------------------------------------------------------
--
--               Idris: Programming with first-class types
--                   [PRL-sem-jr, Artem Pelenitsyn]
--------------------------------------------------------------------------------

--
--  Part 1: Type-level functions: calculating types
--  [Ch.6, sec. 1]
--

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int


getStringOrInt : (isInt: Bool) -> StringOrInt isInt
getStringOrInt False = "Nine"
getStringOrInt True = 9

--
--  Part 2: Application: Variable length arguments functions
--  [Ch.6, sec. 2]
--
-- adding `n` numbers passed as arguments
{-
    adder 0 : Int -> Int
    adder 1 : Int -> Int -> Int
    adder 2 : Int -> Int -> Int -> Int
-}

AdderType : (numargs : Nat) -> Type
AdderType Z = Int
AdderType (S k) = Int -> AdderType k

adder : (numargs : Nat) -> Int -> AdderType numargs
adder Z acc = acc
adder (S k) acc = \n => adder k (acc + n)


-- Type-safe Printf
-- printf "%s number %d" "Page" 94
--    -> "Page number 94"

data Format = Number Format
            | Str Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType (Number x) = Int -> PrintfType x
PrintfType (Str x) = String -> PrintfType x
PrintfType (Lit x y) = PrintfType y
PrintfType End = String

printf : (f : Format) -> String -> PrintfType f
printf (Number y) acc   = \n => printf y (acc ++ show n)
printf (Str y) acc      = \s => printf y (acc ++ s)
printf (Lit y z) acc    = printf z (acc ++ y)
printf End acc          = acc

-- printf (Str (Lit " number " (Number End))) "" "Page" 94
--   -> "Page number 94" : String

--
--  Part 3: Dependent types and I/O
--  [Ch.5, sec. 3]
--

fourInts : Vect 4  Int
fourInts = [0, 1, 2, 3]

-- Reading a Vect of _known_ length from the console
readVectLen : (len : Nat) -> IO (Vect len String)
readVectLen Z = pure []
readVectLen (S k) = do
                        s <- getLine
                        vs <- readVectLen k
                        pure (s :: vs)

-- > :exec readVectLen 2 >>= printLn
-- abc
-- def
-- ["abc", "def"]

-- Reading a Vect of unknown length from the console
-- returning a _dependent pair_ (** type operator)
readVect : IO (len ** Vect len String)
readVect = do
        s <- getLine
        if s == ""
            then pure (_ ** []) -- can use 0 instead of _ but Idris guessed
            else do (_ ** vs) <- readVect
                    pure (_ ** s :: vs)

-- Validating Vect lengths
{-
    1 Read two input vectors, using readVect .
    2 If they have different lengths, display an error.
    3 If they have the _same lengths_, display the result of zipping the vectors together using `zip`:

        zip : Vect n a -> Vect n b -> Vect n (a, b)
-}
zipInputs : IO ()
zipInputs = do
    (n1 ** vs1) <- readVect
    (n2 ** vs2) <- readVect
    -- if n1 == n2 -- won't work, cause type checker doesn't believe in `==`
    case exactLength n1 vs2 of
        Just vs2' => print (zip vs1 vs2')
        Nothing  => print "Error: vectors should be of equal length!"

{-
Note:
exactLength : (len : Nat) -> (xs : Vect m a) -> Maybe (Vect len a)

The definition of `exactLength` is the whole other story, cf. Chap. 8 , sec. 1.
It rises the question about proving things on the type level.
-}

{- Usage:
> :exec zipInputs >>= println
abc
def

123
456

[("abc", "123"), ("def", "456")]
-}
