import Data.Vect

%default total 

{- Types can be treat in same way as the values. -}
returnType : Nat -> Type
returnType Z = Int
returnType (S Z) = String
returnType (S (S n)) = Int -> Int -> Int


{- We can return Int, String or function based on input value -}
valueType : (n : Nat) -> returnType n
valueType Z = 1
valueType (S Z) = "Hello World"
valueType (S (S n)) = \x => \y => x + y

{- Let's extend this idea to variable length input -} 

variableType : (n : Nat) -> Type -> Type
variableType Z type = type
variableType (S k) type = type -> variableType k type

{- This function constructs a type level function
λΠ> variableType 0 
variableType 0 : Type -> Type
λΠ> variableType 0 Int
Int : Type
λΠ> variableType 1 INT
When checking an application of function Main.variableType:
        No such variable INT
λΠ> variableType 1 Int
Int -> Int : Type
λΠ> variableType 2 Int
Int -> Int -> Int : Type
λΠ> variableType 3 String
String -> String -> String -> String : Type -}


variableValue : (n : Nat) -> (x : Type) -> (f : x -> x -> x) -> (y : x) ->  variableType n x
variableValue Z x f y = y 
variableValue (S k) x f y = \inp => variableValue k x f (f inp y)

{- 
λΠ> :t variableValue 0 Int (+) 
variableValue 0 Int (+) : Int -> Int

λΠ> variableValue 1 Int (+) 2 3
5 : Int
λΠ> variableValue 1 String (++) "Hello" "World"
"WorldHello" : String 
-}

{- 
printf "Hello!" : String
printf "Answer: %d" : Int -> String
printf "%s number %d" : String -> Int -> String

-}

{-  This function does not work because of reduction problem, 
    so try parsing string into AST -}
printfType : List Char  -> Type
printfType [] = String
printfType ('%' :: 'd' :: rest)  = Int -> printfType rest
printfType ('%' :: 's' :: rest) = String -> printfType rest
printfType (c :: rest)  = printfType rest 


{- construct value level function -}
printfValue : (xs : List Char) -> String -> printfType xs
printfValue [] acc = acc
printfValue ('%' :: 'd' :: rest) acc = \x => printfValue rest (acc ++ show x)
printfValue ('%' :: 's' :: rest) acc = \x => printfValue rest (acc ++ x)
printfValue (c :: rest) acc = ?acc --  printfValue rest (acc ++ singleton c)

{- It works, but useless because last one is not reducing 
λΠ> printfValue (unpack "%s%d%s") "" "hello" 2 "world"
"hello2world" : String
-}



data Format = FInt Format
            | FString Format
            | FOther Char Format
            | FEnd

format : List Char -> Format
format [] = FEnd
format ('%' :: 'd' :: cs ) = FInt (format cs)
format ('%' :: 's' :: cs ) = FString (format cs)
format (c :: cs)         = FOther c (format cs)

interpFormat : Format -> Type
interpFormat FEnd = String
interpFormat (FInt f)     = Int -> interpFormat f
interpFormat (FString f)  = String -> interpFormat f
interpFormat (FOther _ f) = interpFormat f


formatString : String -> Format
formatString s = format (unpack s)


toFunction : (fmt : Format) -> (acc : String) -> interpFormat fmt
toFunction FEnd acc = acc
toFunction (FInt f) acc     = \i => toFunction f (acc ++ show i)
toFunction (FString f) acc  = \s => toFunction f (acc ++ s)
toFunction (FOther c f) acc = toFunction f (acc ++ singleton c)


printf : (s : String) -> interpFormat (formatString s)
printf s = toFunction (formatString s) "" 



{- Matrix with n rows and m column -}

Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)

repeat : (n : Nat) -> a -> Vect n a
repeat Z     _ = []
repeat (S n) a = a::repeat n a

transposeM : Matrix m n a -> Matrix n m a
transposeM []      = repeat _ []
transposeM (x::xs) = zipWith (::) x (transposeM xs)


twoByThree : Matrix 2 3 Int
twoByThree = [[1,2,3], 
              [4,5,6]]

threeByTwo : Matrix 3 2 Int
threeByTwo = [[1, 4],
              [2, 5],
              [3, 6]]
              
tProof : (xs : Matrix n m a) -> transposeM (transposeM xs) = xs
tProof xs = ?proofisleftasanexercisetothereader


{- This code is literally copied from memory when I was learning Haskell -}
matrixMultiplication : Num a =>  Matrix m r a -> Matrix r n a -> Matrix m n a 
matrixMultiplication xs ys = [[sum $ zipWith (*) ar bc | bc <- (transposeM ys)] | ar <- xs]
