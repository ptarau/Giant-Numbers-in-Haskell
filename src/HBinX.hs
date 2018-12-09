module HBinX where
import System.CPUTime
import Data.List
import HBin
import System.Random
--import Visuals

mul _ E = E
mul E _ = E

mul x  y | o_ x && o_ y = r2 where
  (n,a) = osplit x
  (m,b) = osplit y
  p1 = add (mul a b) (add a b)
  p2 = otimes (add (s n) (s m)) p1
  r1 = sub p2 x
  r2 = sub r1 y  

mul x y | o_ x && i_ y = add x (mul x (s' y))
mul x y | i_ x && o_ y = add y (mul (s' x) y)

mul x y | i_ x && i_ y = r2 where
  (n,a) = isplit x
  (m,b) = isplit y
  p0 = mul a b
  s0 = s (add a b)
  p1 = add p0 (db s0)
  e1 = itimes (add (s n) (s m)) p1
  e2 = i x
  e3 = i y
  r1 = sub (s (s e1)) e2
  r2 = sub r1 e3

square E = E
square x | o_ x = r where
  (n,a) = osplit x
  p1 = add (square a) (db a)
  p2 = otimes (i n) p1
  r = sub p2 (db x) 
square x | i_ x = r where
  (n,a) = isplit x
  p1 = add (square a) (db (o a))
  p2 = itimes (i n) p1
  r = sub (s (s p2)) (db (i x))

pow _ E = V E []
pow x y | o_ y = mul x (pow (square x) (o' y))
pow x y | i_ y = mul x2 (pow x2 (i' y)) where x2 = square x

div_and_rem x y | LT == cmp x y = (E,x)
div_and_rem x y | y /= E = (q,r) where 
  (qt,rm) = divstep x y
  (z,r) = div_and_rem rm y
  q = add (exp2 qt) z

  divstep n m = (q, sub n p) where
    q = try_to_double n m E
    p = leftshiftBy q m    

  try_to_double x y k = 
    if (LT==cmp x y) then s' k
    else try_to_double x (db y) (s k)   
          
divide n m = fst (div_and_rem n m)
remainder n m = snd (div_and_rem n m)

isqrt E = E
isqrt n = if cmp (square k) n==GT then s' k else k where 
  two = i E
  k=iter n
  iter x = if cmp (absdif r x)  two == LT
    then r 
    else iter r where r = step x
  step x = divide (add x (divide n x)) two    
  
absdif x y = if LT == cmp x y then sub y x else sub x y  

modPow m base expo = modStep expo (V E []) base where
  modStep (V E []) r b  = (mul r b) `remainder` m
  modStep x r b | o_ x = 
    modStep (o' x) (remainder (mul r b) m) 
                   (remainder (square b)  m)
  modStep x r b = modStep (hf x) r 
    (remainder (square b) m)

ll_iter k n m | e_ k = n
ll_iter k n m = fastmod y m where 
   x = ll_iter (s' k) n m
   y = s' (s' (square x))

fastmod k m | k == s' m = E
fastmod k m | LT == cmp k m = k
fastmod k m = fastmod (add q r) m where
  (q,r) = div_and_rem k m

lucas_lehmer (W E []) = True
lucas_lehmer p = e_ (ll_iter p_2 four m) where
  p_2 = s' (s' p)
  four = i (o E)
  m  = exp2 p

dyadicSplit z | o_ z = (E,z)
dyadicSplit z | i_ z = (s x, s (g xs)) where  
  V x xs = s' z
  
  g [] =  E
  g (y:ys) = W y ys

randomNats seed k smallest largest = map t ns  where
  ns :: [Integer]
  ns = take k (randomRs 
    (n smallest,n largest) (mkStdGen seed))

oddPrime k m = all strongLiar as where
  m' = s' m
  as = randomNats k k (W E []) m'
  (l,d) = dyadicSplit m'
 
  strongLiar a = (x == V E []) || 
      (any (== m') (squaringSteps l x)) where
    x = modPow m a d

    squaringSteps E _ = []  
    squaringSteps l x = x:squaringSteps (s' l) 
      (remainder (square x) m)

isProbablyPrime (W E [])  = True
isProbablyPrime (W _ _) = False
isProbablyPrime p = oddPrime 42 p

tl k = o' (snd (dyadicSplit k))

lcons n y = s (otimes n (s' (o y)))

lhd z | o_ z = E
lhd z = s x where V x _ = s' z

syracuse n = tl (add n (i n))

nsyr E = [E]
nsyr n = n : nsyr (syracuse n)

fermat n = s (exp2 (exp2 n))

mersenne p = s' (exp2 p)

perfect p = s (V q [q]) where q = s' (s' p)

-- exponent of the 48-th known Mersenne prime
prime48 = 57885161
-- the actual Mersenne prime
mersenne48 = s' (exp2 (t prime48))

perfect48 = perfect (t prime48)

catalan E = i E
catalan n = s' (exp2 (catalan (s' n)))

genFermatPrime = s (leftshiftBy n k) where 
  n = t (9167433::Integer)
  k = t (27653::Integer)

cullenPrime = s (leftshiftBy n n) where 
  n = t (6679881::Integer)

woodallPrime = s' (leftshiftBy n n) where 
  n = t (3752948::Integer)

prothPrime = s (leftshiftBy n k) where 
  n = t (13018586::Integer)
  k = t (19249::Integer)

sophieGermainPrime = s' (leftshiftBy n k) where 
  n = t (666667::Integer)
  k = t (18543637900515::Integer)

twinPrimes = (s' m,s m) where 
  n = t (666669::Integer)
  k = t (3756801695685::Integer)
  m = leftshiftBy n k

instance Ord T where compare = cmp
instance Num T where
  (+) = add
  (-) = sub
  (*) = mul
  fromInteger = t
  abs = id
  signum E = E
  signum _ = V E []
instance Integral T where
  quot = divide
  div = divide
  rem = remainder
  mod = remainder
  quotRem = div_and_rem
  divMod = div_and_rem
  toInteger = n  
instance Real T where
  toRational = toRational . n
instance Enum T where
  fromEnum = fromEnum . n 
  toEnum = t . f where
    f:: Int->Integer
    f = toEnum
  succ = s
  pred = s'

  
-- some simple performance tests

bm0 = benchmark "2^2^30" (i_ (exp2 (exp2 (t 30))))
  
bm0' = benchmark "2^2^30" (even (2^(2^30)))
  
bm1 = benchmark "ack 3 7 on t" 
  (ack (t (toInteger 3)) (t (toInteger 7)))

bm1' = benchmark "nack 3 7 on Integer" (nack 3 7)
   
-- bm2 = benchmark "v 22 11" (o_ (v 22 11))

-- bm2' = benchmark "nv 22 11" (odd (nv 22 11))
   
bm3 = benchmark "fibo (t 30)" (fibo (t 30))

bm3' = benchmark "nfibo 30" (nfibo 30)

bm4 = benchmark "powers" powers

bm4' = benchmark "npowers" npowers

bm5 = benchmark "fact (t 200)" (fact (t 200))

bm5' = benchmark "nfact 200" (nfact 200)   


bm6 = benchmark "1000-th syracuse" bigSyracuse
     
bm6' = undefined -- crashes

bm7 = benchmark "200 primes" (last (take 200 primes))

bm7' = benchmark "200 primes" (last (take 200 nprimes)) 

   
bm8 = benchmark ("product of 5 large primes, tsize=" ++ show sz) (o_ big) where
  big = foldr mul mersenne48
    [prothPrime,cullenPrime,woodallPrime,sophieGermainPrime]
  sz = n (tsize big)

-- crashes
bm8' = benchmark "product of 5 large primes" (odd big) where
  big :: Integer
  big = foldr (*) (n mersenne48)
    (map n [prothPrime,cullenPrime,woodallPrime,sophieGermainPrime])
   

bm9 = benchmark "2^21 predecessors on T" (last (nums (exp2 (t 21))))

bm9' = benchmark "2^21 predecessors on N" (last (nnums (2^21)))


bm10 = benchmark "sum of first 2^16 on T" (sums (t 16))

bm10' = benchmark "sum of first 2^16 on N" (nsums 16)

    
benchmark mes f = do
  x<-getCPUTime
  print f
  y<-getCPUTime
  let time=(y-x) `div` 1000000000
  return (mes++" :time="++(show time))
  
ack E n  = s n
ack m1 E = ack (s' m1) (s E)
ack m1 n1 = ack (s' m1) (ack m1 (s' n1))

nack :: Integer -> Integer -> Integer
nack 0 n  = n+1
nack m1 0 = nack (m1-1) 1
nack m1 n1 = nack (m1-1) (nack m1 (n1-1))
  
primes = s (s E) : filter is_prime (odds_from three) where
  three = s (s (s E)) 
  odds_from x = x : odds_from (s (s x))
    
  is_prime p = [p]==to_primes p
    
  to_primes n = to_factors n p ps where
    (p:ps) = primes
    
    to_factors n p ps | cmp (square p) n == GT = [n]
    to_factors n p ps | r==E =  
      p : to_factors q p ps where
       (q,r) = div_and_rem n p
    to_factors n p (hd:tl) = to_factors n hd tl

--nprimes :: [Integer]
nprimes = 2 : filter is_prime [3,5..] where
  is_prime p = [p]==to_primes p

  to_primes n|n>1 = 
    to_factors n p ps where (p:ps) = nprimes

  to_factors n p ps | p*p > n = [n]
  to_factors n p ps | 0==n `mod` p = 
    p : to_factors (n `div` p)  p ps 
  to_factors n p ps@(hd:tl) = to_factors n hd tl

powers = mul (mul  (pow (t 2) (pow (t 3) (t 4))) 
 (pow (t 3) (pow (t 4) (t 5)))) (pow (t 4) (pow (t 5) (t 6)))
     
npowers = (*) ((*)  ((^) 2 ((^) 3 4)) ((^) 3 ((^) 4 5))) ((^) 4 ((^) 5 6))

nfibo 0 = 1
nfibo 1 = 1
nfibo n = nfibo (n-2) + nfibo (n-1)
  
fibo E = V E []
fibo (V E []) = V E []
fibo n = add (fibo (s' n')) (fibo n') where n' = s' n  
  
nfact 0 = 1
nfact n = n*nfact (n-1)

fact E = V E []
fact x = mul x (fact (s' x))

{-  
nv n k = repeatBlocks nbBlocks blockSize mask where 
  k' = k+1
  nbBlocks = 2^k'
  blockSize = 2^(n-k')
  mask = 2^blockSize-1

  repeatBlocks 0 _ _ = 0
  repeatBlocks k l mask = 
    if o_ k then r else mask+r where
      r = (repeatBlocks (k-1) l mask)*2^l
-}
 
bigSyracuse = (n.tsize) ((nsyr ((exp2.exp2.exp2.exp2.exp2.exp2) (W E []))!!1000))   



nums E = []
nums k = k : nums (s' k)

nnums 0 = []
nnums k = k : nnums (k-1)
  
  
sums m = foldr add E (nums (s' (exp2 m))) where
 
nsums :: Integer->Integer
nsums m = foldr (+) 0 (nnums (2^m-1)) where

-- sparseSet = (n.bitsize) (from_set (map t [1,2,3,2^2^2,3^3^3]))
      
-- comparison between tsize of product and inputs

 
tsize'= n.tsize.t

mtsize :: Integer->Integer->Integer
mtsize x y = n (tsize (mul (t x) (t y)))

mbsize :: Integer->Integer->Integer
mbsize x y = n (bitsize (mul (t x) (t y)))
 
to3 m = xs where
  xs = [(x,y,tsize' x,tsize' y,mtsize x y)|x<-ns,y<-ns]
  ns = [0..2^m-1]

to2 m = xs where
  xs = [(x,y,(x*y),max (tsize' x) (tsize' y),mtsize x y)|x<-ns,y<-ns]
  ns = [2..2^m]

-- subset where multiplication compresses representations
to2x m = filter f (to2 m) where
  f (_,_,_,sx,sy) = sx>sy

-- deep dual

deep_dual E = E
deep_dual (V x xs) = W (deep_dual x) (map deep_dual xs)
deep_dual (W x xs) = V (deep_dual x) (map deep_dual xs)

beautiful x = x == s y where y = deep_dual x

-- Miller-Rabin test

ptest = map n (filter isProbablyPrime (map t [2..105]))


-- is there an infinite number of beautiful numbers?

-- 3d plot of multiplication for tsize and bitsize

-- Thue-Morse sequence

thue = iterate f (V E []) where
          f x = app x (dual x)

-- dual
thue1 = iterate f (V E []) where
          f x = app (dual x) x


app x y | e_ x = y
app x y | o_ x = o (app (o' x) y)
app x y | i_ x = i (app (i' x) y) 
  
ttest k = map n (take k thue)  

btest k = map to_bbin (take k thue) 

ttest1 k = map n (take k thue1)  

btest1 k = map (reverse.to_bbin) (take k thue1) 

to_bbin x | e_ x = []
to_bbin x | o_ x = 0 : to_bbin (o' x)
to_bbin x | i_ x = 1 : to_bbin (i' x)

{-
T0 = 0.
T1 = 01.
T2 = 0110.
T3 = 01101001.
T4 = 0110100110010110.
T5 = 01101001100101101001011001101001.
T6 = 0110100110010110100101100110100110010110011010010110100110010110.
-}

-- 2, 5, 11, 23, 47
cunningham p = takeWhile isProbablyPrime (iterate f p) where
  f x | i_ x = o x
  f (V x xs) = V (s x) xs

mineFrom first = filter is_chain cs where
  cs = map cunningham (iterate s first)
  is_chain (_:_:_) = True
  is_chain _ = False

n2ns k = f (t k) where
  f E = []
  f (V x xs) = map n (x:xs)
  f (W x xs) = map n (x:xs)
 
bc0 = 21134557682798788929395543627272384099528148402397905562931182410618581657582894778725468461609503823179520

c0 = 141361469

cis x = x : cis (o x)

cis6 = take 6 (cis (t c0))
 
bis x = s' x : s x : bis (db x)

bis12 = take 12 (bis (t bc0))

-- gfigs n2ns (map n cis6)
-- gfigs n2ns [5,7,11,13]  
-- gfigs n2ns [0..15]
  
{-

tplot3d m = plot3d mtsize ns ns where
  ns = [0..2^m-1]
 
bplot3d m = plot3d mbsize ns ns where
  ns = [0..2^m-1] 

-}
  

