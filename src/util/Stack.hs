module Util.Stack where

newtype Stack a = Stack [a] deriving Show

init :: Stack a
init = Stack []

push :: a -> Stack a -> Stack a
push x (Stack xs) = Stack (x:xs)

pop :: Stack a -> (Maybe a, Stack a)
pop (Stack []) = (Nothing, Stack [])
pop (Stack (x:xs)) = (Just x, Stack xs)