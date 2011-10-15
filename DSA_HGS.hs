-- | Implementation of Lattice Attacks on Digital Signature Schemes by N.A. Howgrave-Graham and N.P. Smart

import           Control.Monad
import qualified Control.Monad.State as MS
import           Crypto.Random
import           Data.Bits
import           Data.ByteString        (ByteString)
import qualified Data.ByteString     as B
import qualified Data.Digest.SHA1    as SHA1
import           Data.List
import           Data.Maybe
import           Data.Ratio
import           OpenSSL.BN          as OpenSSL
import qualified OpenSSL.DSA         as OpenSSL

import Debug.Trace

type Signature = (Integer, Integer) -- ^ R, S

data Leakage = Leakage {
    l_signature :: Signature,
    l_q         :: Integer, -- TODO, put in Signature
    l_message   :: Integer,
    l_private   :: Integer
} deriving Show

type RState = MS.StateT SystemRandom IO

-- | Sign a message with the private key
sign :: (ByteString -> ByteString) -> Integer -> Integer -> Integer -> Integer -> ByteString -> RState Leakage
sign hash p g q x m = do
        rng <- MS.get
        -- Recalculate the signature in the unlikely case that r = 0 or s = 0
        case generateMax rng q of
                Left err         -> error "Oops"
                Right (k, rng')  -> do
                        MS.put rng'
                        let kinv = fromJust $ inverse k q
                            r    = modexp g k p `mod` q
                            s    = (kinv * (hm + x * r)) `mod` q
                        if r == 0 || s == 0
                            then sign hash p g q x m
                            else return $ Leakage (r, s) q hm k
        where
                hm        = os2ip $ hash m

data LeakHGS = LeakHGS {
    hgs_l      :: Leakage,
    hgs_mu     :: Integer,
    hgs_lambda :: Integer,
    hgs_z'     :: Integer,
    hgs_z''    :: Integer
}

-- | Leak some bits of private data
leak_hgs :: Integer -> Integer -> Leakage -> LeakHGS
leak_hgs lambda mu l = LeakHGS l mu lambda z' z''
    where
        k            = l_private  l
        (z''__z, z') = splitAtBit k      lambda
        (z'', _)     = splitAtBit z''__z (mu-lambda)

-- | Splits (x_n..x_0) into (x_n..x_s,x_s-1..x_0)
splitAtBit toSplit at = (toSplit `div` (2^at), toSplit `rem` (2^at))

parameters max = do
    keyPair <- OpenSSL.generateDSAParametersAndKey 1024 Nothing -- No optional seed needed here
    return  (  OpenSSL.dsaP keyPair, OpenSSL.dsaG keyPair, OpenSSL.dsaQ keyPair, OpenSSL.dsaPrivate keyPair )

-- | We have to sign all data after digesting it with sha1. SHA1 is required by the DSA standard (FIPS 186-2)
doDigest :: ByteString -> ByteString
doDigest toDigest =
    let digestRaw = SHA1.hash $ B.unpack toDigest :: SHA1.Word160
        -- The digest is actually a rather useless Word160, convert it back to a more useful (strict) ByteString
    in  i2osp {- 20 -} $ SHA1.toInteger digestRaw


randomSignature p g q x max = do -- :: RState Leakage
    -- Get a random message
    msg <- MS.liftIO $ OpenSSL.randIntegerOneToNMinusOne max
    sign doDigest p g q x $ i2osp msg

-- Given the leakage, and the data for the 'end' values (index 'h'), compute v_i and w_i
-- Always assume all lambdas and mus are equal among different is
getCoefficients :: LeakHGS -> LeakHGS -> (Integer, Integer)
getCoefficients lhgs_h lhgs_i = (v_i `mod` q, w_i `mod` q)
    where
        ll     = hgs_l lhgs_i
        mu     = hgs_mu lhgs_i
        lambda = hgs_lambda lhgs_i
        z'_i   = hgs_z' lhgs_i
        z''_i  = hgs_z'' lhgs_i

        ll_h   = hgs_l lhgs_h
        m_h    = l_message ll_h
        z'_h   = hgs_z' lhgs_h
        z''_h  = hgs_z'' lhgs_h
        (r_h, s_h) = l_signature ll_h

        q          = l_q ll
        (r_i, s_i) = l_signature ll
        m_i        = l_message ll
        invq       = \x -> fromJust $ inverse x q

        cc_i       = cc r_i s_i
        dd_i       = dd m_i s_i

        cc_h       = cc r_h s_h
        dd_h       = dd m_h s_h

        cc r s     = - r * (invq s)
        dd m s     = - m * (invq s)

        aa_i = -cc_i * (invq cc_h)
        bb_i = -cc_i*dd_h*(invq cc_h) + dd_i

        v_i     = aa_i
        w_i     = (z''_i*2^mu + z'_i+aa_i*z''_h*2^mu+aa_i*z'_h + bb_i) * (invq $ 2^(lambda))


allCoefficients :: [LeakHGS] -> [(Integer, Integer)]
allCoefficients list = map go $ take (h-1) list
    where
        h          = length list
        leak_h     = list !! (h-1)
        go         = getCoefficients leak_h

mmain = do
    let m        = 2^1024
        nrSigs   = 10
        minBit   = 50
        maxBit   = 70
        leakfun  = leak_hgs minBit maxBit
    -- Generate some random parameters
    (p, g, q, alpha) <- parameters m
    rnd              <- newGenIO :: IO SystemRandom
    leaks            <- flip MS.evalStateT rnd $ replicateM nrSigs $ randomSignature p g q alpha m

    let len = length leaks
        h   = leaks !! (len - 1)
        m_h        = l_message h
        (r_h, s_h) = l_signature h
        k_h        = l_private h

    forM leaks $ \leak -> do
        let k_i             = l_private leak
            (z''_i__z_i, _) = splitAtBit k_i 50
            (_, z_i)        = splitAtBit z''_i__z_i (70-50)
        putStrLn $ "secret part is: " ++ show z_i

    let leaked  = map leakfun leaks
        (v, w)  = unzip $ allCoefficients leaked
        lmat    = ntlLattice v q
        tvec    = ntlVec w
    putStrLn $ lmat ++ tvec
    putStrLn $ show $ length leaks
    putStrLn $ show $ length v
    putStrLn $ "// Ephemeral keys are " ++ (concat $ intersperse " " $ flip map leaks $ \ (Leakage _ _ _ private) -> show private)
    putStrLn $ "// q is " ++ show q
    forM leaked $ \l -> putStrLn $ printComputePrivate l

printComputePrivate :: LeakHGS -> String
printComputePrivate lhgs = show z' ++ " + (2^" ++ show mu ++ ")*(" ++ show z'' ++ ") + (2^" ++ show lambda ++ ")*"
    where
    mu     = hgs_mu lhgs
    lambda = hgs_lambda lhgs
    z'     = hgs_z' lhgs
    z''    = hgs_z'' lhgs

-- | Prints code to generate the lattice in NTL, given the $s_i$ and p.
ntlLattice :: [Integer] -> Integer -> String
ntlLattice v_i p = row1 ++ diag
    where
        len  = length v_i
        row1 = concat $ flip map (zip [0..] $ (-1) : v_i) $ \(j, el) -> "l[0][" ++ show j ++ "] = to_ZZ(\"" ++ show el ++ "\"); "
        diag = concat $ flip map [1..len] $ \j -> "l[" ++ show j ++ "][" ++ show j ++ "] = to_ZZ(\"" ++ show p ++ "\"); "

-- | Prints the t vector
ntlVec :: [Integer] -> String
ntlVec w = concat $ flip map (zip [0..len] $ 0 : w) $ \(j, el) -> "t[" ++ show j ++ "] = to_ZZ(\"" ++ show el ++ "\"); "
    where
        len = length w

-- BEGIN HELPERS
-- | check if a list of integer are all even
areEven :: [Integer] -> Bool
areEven = and . map even

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

euclid :: Integral a => a -> a -> a
euclid x y = f 1 0 x 0 1 y where
       f a b g u v w | w == 0    = mod a y
                     | otherwise = f u v w (a-q*u) (b-q*v) (g-q*w)
                       where q = div g w

-- | inverse computes the modular inverse as in g^(-1) mod m
inverse :: Integral a => a -> a -> Maybe a
inverse x m | gcd x m == 1 = Just $ euclid x m
            | otherwise    = Nothing -- "divisor must be coprime to modulus"

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

-- END HELPERS