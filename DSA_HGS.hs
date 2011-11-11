-- | Implementation of Lattice Attacks on Digital Signature Schemes by N.A. Howgrave-Graham and N.P. Smart

import           Control.Monad
import qualified Control.Monad.State as MS
import           Crypto.Random
import           Data.Array
import           Data.Bits
import           Data.ByteString        (ByteString)
import qualified Data.ByteString     as B
import qualified Data.Digest.SHA1    as SHA1
import           Data.List
import           Data.Maybe
import           Data.Helpers
import           Data.Ratio
import           Math.Lattices.LLL
import           Math.Modular
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
        nrSigs   = 4
        minBit   = 0
        maxBit   = 100
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

    let leaked  = map leakfun leaks
        (v, w)  = unzip $ allCoefficients leaked
        lmat    = ntlLattice v q
        tvec    = ntlVec w

        l       = len - 1
        row0    = (-1) : (take l v)
        other r = 0:[ el | i <- [0..l-1], let el = if r == i + 1 then q else 0 ]
        lattice = row0:[ other i | i <- [1..l] ]
        t       = 0:w

        reduced = lll $ map (map toRational) lattice
        reduced'= [ reduced ! i | i <- [0..l] ]
        z       = closeVector reduced' $ map toRational t

        computed= computePrivate (leaked !! (length leaked - 1)) $ numerator $ head z

    putStrLn $ "private key should be: " ++ show alpha
    putStrLn $ "And we compute it as:  " ++ show computed
    putStrLn $ "Difference: " ++ show (alpha - computed)

computePrivate :: LeakHGS -> Integer -> Integer
computePrivate lhgs_h z_h = private
    where
        k_h     = z' + (2^mu)*(z'') + (2^lambda)* z_h
        private = ((s_h * k_h - m_h ) * invr_h) `mod` q

        mu         = hgs_mu lhgs_h
        lambda     = hgs_lambda lhgs_h
        h          = hgs_l lhgs_h
        (r_h, s_h) = l_signature h
        m_h        = l_message h
        z'         = hgs_z' lhgs_h
        z''        = hgs_z'' lhgs_h
        q          = l_q h
        invr_h     = fromJust $ inverse r_h q

printComputePrivate :: LeakHGS -> String
printComputePrivate lhgs_h =   "k_h     = " ++ show z' ++ " + (2^" ++ show mu ++ ")*(" ++ show z'' ++ ") + (2^" ++ show lambda ++ ")* z_h\n"
                            ++ "private = ((" ++ show s_h ++ " * k_h - " ++ show m_h ++ ") * " ++ show invr_h ++ ") `mod` " ++ show q
    where
        mu         = hgs_mu lhgs_h
        lambda     = hgs_lambda lhgs_h
        h          = hgs_l lhgs_h
        (r_h, s_h) = l_signature h
        m_h        = l_message h
        z'         = hgs_z' lhgs_h
        z''        = hgs_z'' lhgs_h
        q          = l_q h
        invr_h     = fromJust $ inverse r_h q

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
