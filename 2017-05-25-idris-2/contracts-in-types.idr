--============================================================================--
-- PL-Junior Seminar
--
-- May 25, 2017
-- Julia Belyakova
--
--                       Idris :: Part 2
--                       Assumptions and Contracts in Types
--
-- Chapters 8, 9
--============================================================================--

--------------------------------------------------------------------------------
-- Algebraic Data Types
-- in two styles
--------------------------------------------------------------------------------

----------- Classic ADT Style

--{-
data Nat' =
    ZZ
  | SS Nat'
---}

----------- GADT Style (Generalized Algebraic Data Types)

{-
data Nat' : Type where
  ZZ : Nat'
  SS : Nat' -> Nat'
-}

n0 : Nat'
n0 = ZZ

n2 : Nat'
n2 = SS (SS ZZ)


------------ ADT Style

data WrapperA ty =
  WrapN Nat

{-
data WrapperA ty : Type where
  WrapN : Nat -> WrapperA ty
-}

wa1 : WrapperA Nat
wa1 = WrapN 5

wa2 : WrapperA Bool
wa2 = WrapN 101

-- Note!
-- We can create a value of type [WrapperA ty]
-- for _any_ type [ty].

total
makeWrapperA : (ty : Type) -> WrapperA ty
makeWrapperA ty = WrapN 42

{-
idris > makeWrapperA String
WrapN 42 : WrapperA String

idris > makeWrapperA Nat'
WrapN 42 : WrapperA Nat'
-}

testWrapperA : WrapperA ty -> Nat
testWrapperA (WrapN k) = k


------------ GADT Style

{-
data WrapperA ty =
  WrapN Nat
-}

data Wrapper : Type -> Type where
  WrapNat  : Nat -> Wrapper Nat
  WrapBool : Wrapper Bool
  WrapStr  : Int -> Wrapper String

-- Note!
-- We can only create values of type [Wrapper ty]
-- for [ty] equal to [Int], [Bool], or [String].

makeWrapperString : Wrapper String
makeWrapperString = WrapStr 0

-- There is no way to complete [makeWrapper].

--makeWrapper : Wrapper ty


testWrapperString : Wrapper String -> Int
testWrapperString (WrapStr x) = x

testWrapperBool : Wrapper Bool -> Int
testWrapperBool WrapBool = -1

-- There are no values of type [Wrapper (List Nat)]!
-- The first argument is as a _contradiction_.

testWrapperListNat : Wrapper (List Nat) -> Int
testWrapperListNat (WrapNat _) impossible
testWrapperListNat WrapBool impossible
testWrapperListNat (WrapStr _) impossible



--------------------------------------------------------------------------------
-- Empty type
--------------------------------------------------------------------------------

-- [Void : Type] is the empty type
-- (False proposition)

{-
data Void : Type where
-}

-- We can prove False (Void) from contradiction.

total
makeVoid : Wrapper Nat' -> Void
makeVoid (WrapNat _) impossible
makeVoid WrapBool impossible
makeVoid (WrapStr _) impossible

-- In constructive logic
-- negation [~ P] is actually defined as [P -> False].
-- In our case it's [P -> Void].



--------------------------------------------------------------------------------
-- Dependent Types
--------------------------------------------------------------------------------

-- [Foo] is a _dependent_ type:
-- it depends on a _value_ of type [Nat].

data Foo : Nat -> Type where
  Bar : Foo 42
  Baz : Bool -> Foo 666

testFoo42 : Foo 42 -> Nat
testFoo42 Bar = 42

testFoo666 : Foo 666 -> Nat
testFoo666 (Baz x) = 666

-- Again, we can prove Void from contradiction [Foo 10]:

testFoo10 : Foo 10 -> Void
testFoo10 Bar impossible
testFoo10 (Baz _) impossible

-- But we cannot complete this function:

testFoo42' : Foo 42 -> Void
testFoo42' Bar = ?testFoo42'_rhs_1


------------ Vector

-- Classic example of vector type,
-- which provides information about amount of elements

data Vect' : (len : Nat) -> (ty : Type) -> Type where
  Nil'  : Vect' Z ty
  Cons' : ty -> Vect' len ty -> Vect' (S len) ty

v0 : Vect' Z String
v0 = Nil'

v2 : Vect' 2 String
v2 = Cons' "hello" (Cons' "Idris" Nil')



--------------------------------------------------------------------------------
-- Equality
--------------------------------------------------------------------------------

-- With GADT style and dependent types
-- we have enough power to encode
-- _properties_ of values in _types_.

data EqNat : Nat -> Nat -> Type where
  ReflNat : EqNat n n

-- Value of type [EqNat n m]
-- is a proof "n is equal to m".

makeEqNat5_5 : EqNat 5 5
makeEqNat5_5 = ReflNat

testEqNat5_4 : EqNat 5 4 -> Void
testEqNat5_4 ReflNat impossible


-- Function [subVecs] returns pointwise sum
-- of two vectors of the same length

sumVecs : (xs : Vect' n Nat) -> (ys : Vect' m Nat)
          -> (eqLen : EqNat n m) -> Vect' n Nat
sumVecs Nil' Nil' eqLen = Nil'
sumVecs Nil' (Cons' _ _) ReflNat impossible
sumVecs (Cons' _ _) Nil' ReflNat impossible
sumVecs (Cons' x y) (Cons' z w) ReflNat =
  Cons' (x + z) (sumVecs y w ReflNat)


vn1 : Vect' 1 Nat
vn1 = Cons' 5 Nil'

vn2 : Vect' 2 Nat
vn2 = Cons' 3 vn1

vn2' : Vect' 2 Nat
vn2' = Cons' 7 (Cons' 2 Nil')

{-
idris > sumVecs vn2 vn2' ReflNat
Cons' 10 (Cons' 7 Nil') : Vect' 2 Nat

idris > sumVecs vn2 vn1 ReflNat
(input):1:9:When checking argument eqLen to function Main.sumVecs:
        Type mismatch between
                EqNat n n (Type of ReflNat)
        and
                EqNat 2 1 (Expected type)

        Specifically:
                Type mismatch between
                        1
                and
                        0
-}


------------ Computing proof of Nat equality

sameS : (n : Nat) -> (m : Nat) -> EqNat n m -> EqNat (S n) (S m)
sameS m m ReflNat = ReflNat

checkEqNat : (n : Nat) -> (m : Nat) -> Maybe (EqNat n m)
checkEqNat Z Z = Just ReflNat
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) =
  case checkEqNat k j of
    Nothing    => Nothing
    Just eqPrf => Just (sameS k j eqPrf)

{-
idris > checkEqNat 3 (10 - 7)
Just ReflNat : Maybe (EqNat 3 3)

idris > checkEqNat 3 5
Nothing : Maybe (EqNat 3 5)
-}


-- Property is decidable if it is possible to determine
-- whether it holds or not.

data Decidable : (prop : Type) -> Type where
  Yes : (prf : prop) -> Decidable prop
  No  : (contra : prop -> Void) -> Decidable prop

-- Aux lemmas

zeroNotSuc : (EqNat 0 (S k)) -> Void
zeroNotSuc ReflNat impossible

sucNotZero : (EqNat (S k) 0) -> Void
sucNotZero ReflNat impossible

eqSucc_eq_contra : (contra : EqNat n m -> Void) -> (EqNat (S n) (S m)) -> Void
eqSucc_eq_contra contra ReflNat = contra ReflNat

-- For any pair of natural numbers
-- we can decide if they are equal

decEqNat : (n : Nat) -> (m : Nat) -> Decidable (EqNat n m)
decEqNat Z Z = Yes ReflNat
decEqNat Z (S k) = No zeroNotSuc
decEqNat (S k) Z = No sucNotZero
decEqNat (S k) (S j) =
  case decEqNat k j of
    Yes prf    => Yes (sameS k j prf)
    No  contra => No  (eqSucc_eq_contra contra)


-- [zipEqLen] returns zip of two lists if they are of equal length
-- together with proof of equality.
-- If lists are of different length, it returns Nothing.

zipEqLen : (xs : List ty1) -> (ys : List ty2)
           -> Maybe (List (ty1, ty2), EqNat (length xs) (length ys))
zipEqLen xs ys =
  case decEqNat (length xs) (length ys) of
    Yes prf => Just (zip xs ys, prf)
    No => Nothing

{-
idris > zipEqLen [1,2,3] ["a", "b", "c"]
Just ([(1, "a"), (2, "b"), (3, "c")],
      ReflNat) : Maybe (List (Integer, String), EqNat 3 3)

idris > zipEqLen [1,2,3] ["a", "b"]
Nothing : Maybe (List (Integer, String), EqNat 3 2)
-}


------------ Standard Equality definition:

{-
data (=) : ty1 -> ty2 -> Type where
  Refl : x = x
-}

{-
idris > the (3 = 1 + 2) Refl
Refl : 3 = 3

idris > the (3 = 4) Refl
(input):1:5:When checking argument value to function Prelude.Basics.the:
        Type mismatch between
                4 = 4 (Type of Refl)
        and
                3 = 4 (Expected type)

        Specifically:
                Type mismatch between
                        4
                and
                        3

-}



--------------------------------------------------------------------------------
-- More Contracts in Types
--------------------------------------------------------------------------------

-- Let's define a property
-- "[n] is strictly less than [m]"

data LT' : (n, m : Nat) -> Type where
  LT'Succ : LT' n (S n)
  LT'Step : (lt : LT' n m) -> LT' n (S m)

-- This definition corresponds to the following inference rules:
{-
      --------------- (Succ)
         n < S n

          n < m
      --------------- (Step)
         n < S m
-}


-- evidence for [1 < 3]

lt_1_3 : LT' 1 3
lt_1_3 = LT'Step LT'Succ

{-
    ---------- (Succ)
      1 < 2
    ---------- (Step)
      1 < 3
-}


-- Now we can use this property to define a function
-- which returns Nth element of a list
-- if N less than length of the list

-- getNth : (n : Nat) -> (xs : List ty) -> (nLtLen : LT' n (length xs)) -> ty


-- Aux lemmas

ltS_lt : (ltS : LT' (S n) m) -> LT' n m
ltS_lt LT'Succ = LT'Step LT'Succ
ltS_lt (LT'Step lt) =
  let ltnm = (ltS_lt lt) in
  LT'Step ltnm

ltSS_lt : (ltSS : LT' (S n) (S m)) -> LT' n m
ltSS_lt LT'Succ = LT'Succ
ltSS_lt (LT'Step lt) = ltS_lt lt

-- The function

getNth : (n : Nat) -> (xs : List ty) -> (nLtLen : LT' n (length xs)) -> ty
-- it is not possible that 0 < 0 (because length [] = 0)
getNth Z [] LT'Succ impossible
getNth Z [] (LT'Step _) impossible
-- this case is ok: return head of the list
getNth Z (x :: xs) nLtLen = x
-- it is not possible that S n < 0
getNth (S _) [] LT'Succ impossible
getNth (S _) [] (LT'Step _) impossible
-- here we have to prove that k < length xs
-- given that [nLtLen : S k < length (x :: xs)]
getNth (S k) (x :: xs) nLtLen =
  getNth k xs (ltSS_lt nLtLen)

-- We can ask Idris to build a proof of [LT' n (length xs)]

getNth' : (n : Nat) -> (xs : List ty) -> {auto goodN : LT' n (length xs)} -> ty
getNth' n xs {goodN} = getNth n xs goodN

{-
idris > getNth' 2 [10,11,12,13]
12 : Integer

idris > getNth' 7 [10,11,12,13]
(input):1:9:When checking argument goodN to function Main.getNth':
        Can't find a value of type
                LT' 7 4
-}

elem0 : Nat
elem0 = getNth' 0 [10,11,12,13]

{-
idris > elem0
10 : Nat
-}

elem2 : String
elem2 = getNth' 2 ["a", "b", "c", "d"]

{-
idris > elem2
"c" : String
-}
