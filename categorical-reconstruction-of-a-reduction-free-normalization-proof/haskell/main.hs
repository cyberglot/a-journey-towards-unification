module Main where

data Ty = O          -- base type
        | Ty :--> Ty -- function type
        deriving Show

-- debruijn indexed terms
data Tm = Var0 
        | VarS Tm 
        | Lam Tm 
        | App Tm Tm 
        deriving Show

-- weakening ????
data Wk = WId 
        | W1 Wk 
        | W2 Wk 
        deriving Show

-- what does Vl mean?
data Vl = VO Tm  -- V of object
        | VArr (Wk -> Vl -> Vl)  -- V of arrow
        deriving Show

wPi :: Wk
wPi = W1 WId

-- weakening of basic types???
-- why is uninterpreted basic type necessary here?
oWk :: Wk -> Wk -> Wk
oWk WId w = w
oWk (W1 w) w' = W1 (oWk w w')
oWk (W2 w) WId = W2 w
oWk (W2 w) (W1 w') = W1 (oWk w w')
oWk (W2 w) (W2 w') = W2 (oWk w w')

-- weakening of terms
wkTm :: Wk -> Tm -> Tm
wkTm WId m = m
wkTm w (Lam m) = Lam (wkTm (W2 w) m)
wkTm w (App m1 m2) = App (wkTm w m1) (wkTm w m2)
wkTm (W2 w) (VarS m) = wkTm w m
wkTm (W2 w) Var0 = Var0
wkTm (W1 w) m = VarS (wkTm w m)

wkVl :: Wk -> Vl -> Vl
wkVl w (VO m) = VO (wkTm w m)
wkVl w (VArr f) = VArr (\w' x -> f (oWk w w') x)

wkVls :: Wk -> [Vl] -> [Vl]
wkVls w xs = map (wkVl w) xs

-- wtf does q mean?
q :: Ty -> Vl -> Tm
q O (VO m) = m
q (s :--> t) (VArr f) = Lam (q t (f wPi (u t Var0)))
  where
    u :: Ty -> Tm -> Vl
    u O m = VO m
    u (s :--> t) m = VArr (\w x -> u t (App (wkTm w m) (q s x)))

eval :: Tm -> [Vl] -> Vl
eval Var0 (x:xs) = x
eval (VarS m) (x:xs) = eval m xs
eval (Lam m) xs = VArr (\w x -> eval m (x : wkVls w xs))
eval (App m1 m2) xs =
  case eval m1 xs of
    VArr f -> f WId (eval m2 xs)

idG :: [Ty] -> [Vl]
idG [] = []
idG (s : g) = (u s Var0) : wkVls wPi (idG g)
  where
    -- wtf does u mean?
    u :: Ty -> Tm -> Vl
    u O m = VO m
    u (s :--> g) m = VArr (\w x -> u g (App (wkTm w m) (q s x)))

nf :: [Ty] -> Ty -> Tm -> Tm
nf gamma _type term = q _type (eval term (idG gamma))

main :: IO ()
main = do
  putStrLn "Hello, world!"