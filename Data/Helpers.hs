-- | Some helper functions to deal with binary and random data
module Data.Helpers (
    os2ip,
    i2osp,
    lengthBytes,
    Error(..),
    generateMax
) where

import           Crypto.Random
import           Data.Bits
import           Data.ByteString        (ByteString)
import qualified Data.ByteString     as B

-- | os2ip converts a byte string into a positive integer
os2ip :: ByteString -> Integer
os2ip = B.foldl' (\a b -> (256 * a) .|. (fromIntegral b)) 0

-- | i2osp converts a positive integer into a byte string
i2osp :: Integer -> ByteString
i2osp m = B.reverse $ B.unfoldr divMod256 m
        where
                divMod256 0 = Nothing
                divMod256 n = Just (fromIntegral a,b) where (b,a) = n `divMod` 256

-- | returns the number of bytes to store an integer with i2osp
lengthBytes :: Integer -> Int
lengthBytes n
        | n < 256   = 1
        | otherwise = 1 + lengthBytes (n `div` 256)

data Error =
          InvalidSignature          -- ^ signature is not valid r or s is not between the bound 0..q
        | RandomGenFailure GenError -- ^ the random generator returns an error. give the opportunity to reseed for example.
        deriving (Show,Eq)

-- | generate a positive integer between 0 and m.
-- using as many bytes as necessary to the same size as m, that are converted to integer.
generateMax :: CryptoRandomGen g => g -> Integer -> Either GenError (Integer, g)
generateMax rng m = case genBytes (lengthBytes m) rng of
    Left err         -> Left err
    Right (bs, rng') -> Right (os2ip bs `mod` m, rng')
