module Normalisation where

import Prelude
import Lambda

fresh_for_term:: Term -> Variable
fresh_for_term t = fresh_var 0 t
    
fresh_var:: Int -> Term -> Variable
fresh_var x t = case (fresh (var x) t) of
    True ->  var x
    False -> fresh_var (x+1) t

-- Substitution
substitute :: Variable -> Term -> Term -> Term
substitute v x (VTm t)
    | v == t = x
    | otherwise = VTm t
substitute v x (FTm v1 t1) 
    | v == v1 = (FTm v1 t1)
    | (v /= v1) && (not (free v t1)) = (FTm v1 t1)
    | (v /= v1) && (free v t1) && (not (free v t1)) = (FTm v1 (substitute v x t1))
    | otherwise = FTm z (substitute v x (substitute v1 (VTm z) t1)) where z = (fresh_for_term t1)
substitute v x (ATm t1 t2) = ATm (substitute v x t1) (substitute v x t2)

eta_redex_helper::Term->Int->Bool
eta_redex_helper (FTm _ t) 1 = eta_redex_helper t 2
eta_redex_helper (ATm t1 (VTm x)) 2 = not $ free x t1
eta_redex_helper _ _ = False

alpha_conversion::Term->Term
alpha_conversion (FTm x t) = substitute x (VTm (fresh_for_term t)) t 
alpha_conversion t = t

eta_redex:: Term -> Bool
eta_redex t = eta_redex_helper t 1

beta_redex::Term->Bool
beta_redex (ATm (VTm v) t1) = True
beta_redex t = False

beta_reduction::Term->Term
beta_reduction (VTm v)   = VTm v
beta_reduction (FTm x t) = FTm x (beta_reduction t)
beta_reduction (ATm t1 t2)       = apply (beta_reduction t1) (beta_reduction t2)

apply::Term->Term->Term
apply (FTm x t1) t2 = beta_reduction $ rename x t2 t1
apply t1 t2 = ATm t1 t2

fmap'::(Term->Term)->Term->Term 
fmap' f (VTm v) = f (VTm v)
fmap' f (FTm v t) = FTm v (fmap' f t)
fmap' f (ATm t1 t2) = ATm (fmap' f t1) (fmap' f t2)
 
rename :: Variable-> Term->Term->Term
rename a t1 t2 = fmap' replace t2
    where replace = \(VTm x) -> if x == a then t1 else (VTm x)



normal_reduction::Term->Term
normal_reduction (ATm t1 t2) = beta_reduction $ ATm (beta_reduction t1) (beta_reduction t2)
normal_reduction (FTm v t) = FTm v (beta_reduction t)
normal_reduction (VTm v) = VTm v
