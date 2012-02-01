{-# LANGUAGE OverloadedStrings, FlexibleInstances #-}
module EDSL where

import Pretty
import Syntax

import Data.Char
import GHC.Exts( IsString(..) )

var  = Var . Fre
fun  = flip Fun []
con  = flip Con []
pVa  = PVa
(+$) v w = POp Pl (Fre v) (Fre w)
(-$) v w = POp Mi (Fre v) (Fre w)
(==$) v w = POp Eq (Fre v) (Fre w)
(<=$) v w = POp Le (Fre v) (Fre w)
(/=$) v w = POp Ne (Fre v) (Fre w)
seqq v w = POp Seq (Fre v) (Fre w)
x @: vs = x :@ map Fre (words vs)
letIn bs x = Let (map snd bs) (abstract' (map fst bs) x)
(=:) = (,)
caseOf x as = Case x as
(-->) p y = (c, length vs) :-> abstract' vs y
  where (c:vs) = words p
lam p x = Lam (length vs) (abstract' vs x)
  where vs = words p                   

infix 8 =:
infix 8 -->
  
instance IsString (Expr String) where
  fromString xs@(x:_) | isLower x = var xs
                      | otherwise = con xs

example = Prog
 [ lam "" $ letIn ["inc" =: fun 2, "xs" =: "Nil"]
              $ letIn ["xs'" =: fun 1 @: "inc xs"]
                $ fun 1 @: "inc xs'"
 , lam "f x" $ caseOf "x"
     [ "Nil"       --> "Nil" 
     , "Cons x xs" --> letIn [ "x'"  =:  "f" @: "x"
                             , "xs'" =: fun 1 @: "f xs" ]
                       ("Cons" @: "x' xs'") ]
 , lam "m" $ letIn [ "one" =: pVa 1 ] $ "m" +$ "one" ]
 

