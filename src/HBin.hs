module HBin where
-- import Visuals

data T = E | V T [T]  | W T [T] deriving (Eq,Read,Show)

n E = 0
n (V x []) = 2^(n x +1)-1
n (V x (y:xs)) = (n u+1)*2^(n x + 1)-1 where u = W y xs
n (W x []) = 2^(n x+2)-2
n (W x (y:xs)) = (n u+2)*2^(n x + 1)-2 where u = V y xs  

s E = V E []
s (V E []) =  W E []
s (V E (x:xs)) =  W (s x) xs  
s (V z xs) = W E (s' z : xs)
s (W z [])  = V (s z) []
s (W z [E]) = V z [E]
s (W z (E:y:ys)) = V z (s y:ys)
s (W z (x:xs)) = V z (E:s' x:xs)

s' (V E []) = E
s' (V z []) = W (s' z) []
s' (V z [E]) =  W z [E]
s' (V z (E:x:xs)) =  W z (s x:xs)  
s' (V z (x:xs)) =  W z (E:s' x:xs)  
s' (W E []) = V E []
s' (W E (x:xs)) = V (s x) xs 
s' (W z xs) = V E (s' z:xs)

o E = V E []
o (V x xs) = V (s x) xs
o (W x xs) = V E (x:xs)

i E = W E []
i (V x xs) = W E (x:xs)
i (W x xs) = W (s x) xs

o' (V E []) = E
o' (V E (x:xs)) = W x xs
o' (V x xs) = V (s' x) xs

i' (W E []) = E
i' (W E (x:xs)) = V x xs
i' (W x xs) = W (s' x) xs

e_ E = True
e_ _ = False

o_ (V _ _ ) = True
o_ _ = False

i_ (W _ _ ) = True
i_ _ = False

t 0 = E
t x | x>0 && odd x = o(t (div (pred x) 2))
t x | x>0 && even x = i(t (pred (div x 2)))

db = s' . o
hf = o' . s 

exp2 E = V E []
exp2 x = s (V (s' x) [])

otimes E y = y
otimes n E = V (s' n) []
otimes n (V y ys) = V (add n y) ys
otimes n (W y ys) = V (s' n) (y:ys)

itimes E y = y
itimes n E = W (s' n) []
itimes n (W y ys) = W (add n y) ys
itimes n (V y ys) = W (s' n) (y:ys)    

oplus k x y =  itimes k (add x y) 
   
oiplus k x y = s' (itimes k (s (add x y)))    
   
iplus k x y = s' (s' (itimes k (s (s (add x y)))))

ominus _ x y | x == y = E
ominus k x y = s (otimes k (s' (sub x y))) 

iminus _ x y | x == y = E   
iminus k x y =  s (otimes k (s' (sub x y)))

oiminus k x y | x==s y = s E
oiminus k x y | x == s (s y) = s (exp2 k)
oiminus k x y =  s (s (otimes k (s' (s' (sub x y)))))   

iominus k x y = otimes k (sub x y)

osplit (V x []) = (x,E )
osplit (V x (y:xs)) = (x,W y xs)

isplit (W x []) = (x,E )
isplit (W x (y:xs)) = (x,V y xs)

add E y = y
add x E = x

add x y |o_ x && o_ y = f (cmp a b) where
  (a,as) = osplit x
  (b,bs) = osplit y
  f EQ = oplus (s a) as bs
  f GT = oplus (s b) (otimes (sub a b) as) bs
  f LT = oplus (s a) as (otimes (sub b a) bs)

add x y |o_ x && i_ y = f (cmp a b) where
  (a,as) = osplit x
  (b,bs) = isplit y
  f EQ = oiplus (s a) as bs
  f GT = oiplus (s b) (otimes (sub a b) as) bs
  f LT = oiplus (s a) as (itimes (sub b a) bs)  

add x y |i_ x && o_ y = f (cmp a b) where
  (a,as) = isplit x
  (b,bs) = osplit y
  f EQ = oiplus (s a) as bs
  f GT = oiplus (s b) (itimes (sub a b) as) bs
  f LT = oiplus (s a) as (otimes (sub b a) bs)    

add x y |i_ x && i_ y = f (cmp a b) where
  (a,as) = isplit x
  (b,bs) = isplit y
  f EQ = iplus (s a) as bs
  f GT = iplus (s b) (itimes (sub a b) as) bs
  f LT = iplus (s a) as (itimes (sub b a) bs)  

sub x E = x
sub x y | o_ x && o_ y = f (cmp a b) where
  (a,as) = osplit x
  (b,bs) = osplit y
  f EQ = ominus (s a) as bs
  f GT = ominus (s b) (otimes (sub a b) as) bs
  f LT = ominus (s a) as (otimes (sub b a) bs)

sub x y |o_ x && i_ y = f (cmp a b) where
  (a,as) = osplit x
  (b,bs) = isplit y
  f EQ = oiminus (s a) as bs
  f GT = oiminus (s b) (otimes (sub a b) as) bs
  f LT = oiminus (s a) as (itimes (sub b a) bs)  

sub x y |i_ x && o_ y = f (cmp a b) where
  (a,as) = isplit x
  (b,bs) = osplit y
  f EQ = iominus (s a) as bs
  f GT = iominus (s b) (itimes (sub a b) as) bs
  f _ = iominus (s a) as (otimes (sub b a) bs) 

sub x y |i_ x && i_ y = f (cmp a b) where
  (a,as) = isplit x
  (b,bs) = isplit y
  f EQ = iminus (s a) as bs
  f GT = iminus (s b) (itimes (sub a b) as) bs
  f LT = iminus (s a) as (itimes (sub b a) bs)  

cmp E E = EQ
cmp E _ = LT
cmp _ E = GT
cmp x y | x' /= y'  = cmp x' y' where
  x' = bitsize x
  y' = bitsize y
cmp x y = 
  compBigFirst (reversedDual x) (reversedDual y)

compBigFirst E E = EQ
compBigFirst x y | o_ x && o_ y = f (cmp a b) where
    (a,c) = osplit x
    (b,d) = osplit y
    f EQ = compBigFirst c d
    f LT = GT
    f GT = LT   
compBigFirst x y | i_ x && i_ y = f (cmp a b) where
    (a,c) = isplit x
    (b,d) = isplit y
    f EQ = compBigFirst c d
    f other = other
compBigFirst x y | o_ x && i_ y = LT
compBigFirst x y | i_ x && o_ y = GT

reversedDual E = E
reversedDual (V x xs) = f (len (y:ys)) where
  (y:ys) = reverse (x:xs)
  f l | o_ l = V y ys
  f l | i_ l = W y ys
reversedDual (W x xs) = f (len (y:ys)) where
  (y:ys) = reverse (x:xs)
  f l | o_ l = W y ys
  f l | i_ l = V y ys

len [] = E
len (_:xs) = s (len xs)  

dual E = E
dual (V x xs) = W x xs
dual (W x xs) = V x xs

bitsize E = E
bitsize (V x xs) = s (foldr add1 x xs)
bitsize (W x xs) = s (foldr add1 x xs)

add1 x y = s (add x y)

ilog2 x = bitsize (s' x)

leftshiftBy _ E = E
leftshiftBy n k = s (otimes n (s' k))

toShift x | o_ x = (o E,s a,s b) where
  (a,b) = osplit x
toShift x | i_ x = (i E,s a,s (s b)) where 
  (a,b) = isplit x

rightshiftBy _ E = E
rightshiftBy m k = f (cmp m a) where
  (p,a,b) = toShift k
  
  f EQ | o_ p = sub b p
  f EQ | i_ p = s (sub b p)
  f LT | o_ p = otimes (sub a m) (sub b p)
  f LT | i_ p = s (itimes (sub a m) (sub b p))
  f GT =  rightshiftBy (sub m a) b

tsize E = E
tsize (V x xs) = foldr add1 E (map tsize (x:xs))
tsize (W x xs) = foldr add1 E (map tsize (x:xs))

iterated f E x = x
iterated f k x = f (iterated f (s' k) x) 

bestCase k = iterated wTree k E where wTree x = W x []

worstCase k = iterated (i.o) k E 

worstCase' k = iterated (o.i) k E

