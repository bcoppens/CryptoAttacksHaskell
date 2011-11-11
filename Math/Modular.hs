-- | Some useful functions for modular arithmetic and group operations
module Math.Modular (
    inverse
) where

-- | Extended Euclid's algorithm for computing a multiplicative inverse
euclid :: Integral a => a -> a -> a
euclid x y = f 1 0 x 0 1 y
    where
        f a b g u v w | w == 0    = a `mod` y
                      | otherwise = f u v w (a-q*u) (b-q*v) (g-q*w)
            where
                -- The quotient for the current iteration
                q = g `div` w

-- | Computes the multiplicative inverse of x: x^(-1) mod m
inverse :: Integral a => a -> a -> Maybe a
inverse x m | gcd x m == 1 = Just $ euclid x m
            | otherwise    = Nothing -- "divisor must be coprime to modulus"
