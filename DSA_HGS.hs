-- | Implementation of Lattice Attacks on Digital Signature Schemes by N.A. Howgrave-Graham and N.P. Smart

import           Control.Applicative
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
import           LeakingCrypto.DSA        (l_message, l_signature, l_q)
import qualified LeakingCrypto.DSA     as DSA hiding (l_private)
import qualified LeakingCrypto.DSA     as DSAPrivate (l_private)
import           Math.Lattices.LLL
import           Math.Modular
import           OpenSSL.BN          as OpenSSL
import qualified OpenSSL.DSA         as OpenSSL

import Debug.Trace

data LeakHGS = LeakHGS {
    hgs_l      :: DSA.Leakage,
    hgs_mu     :: Integer,
    hgs_lambda :: Integer,
    hgs_z'     :: Integer,
    hgs_z''    :: Integer
}

-- | Leak some bits of private data
leak_hgs :: Integer -> Integer -> DSA.Leakage -> LeakHGS
leak_hgs lambda mu l = LeakHGS l mu lambda z' z''
    where
        k            = DSAPrivate.l_private  l
        (z''__z, z') = splitAtBit k      lambda
        (z'', _)     = splitAtBit z''__z (mu-lambda)

-- | Splits (x_n..x_0) into (x_n..x_s,x_s-1..x_0)
splitAtBit toSplit at = (toSplit `div` (2^at), toSplit `rem` (2^at))

-- Given the leakage, and the data for the 'end' values (index 'h'), compute v_i and w_i
-- Always assume all lambdas and mus are equal among different is
getCoefficients :: LeakHGS -> LeakHGS -> (Integer, Integer)
getCoefficients lhgs_h lhgs_i = (v_i `mod` q, w_i `mod` q)
    where
        ll         = hgs_l lhgs_i
        mu_i       = hgs_mu lhgs_i
        lambda_i   = hgs_lambda lhgs_i
        z'_i       = hgs_z' lhgs_i
        z''_i      = hgs_z'' lhgs_i

        ll_h       = hgs_l lhgs_h
        m_h        = l_message ll_h
        z'_h       = hgs_z' lhgs_h
        z''_h      = hgs_z'' lhgs_h
        (r_h, s_h) = l_signature ll_h
        lambda_h   = hgs_lambda lhgs_h
        mu_h       = hgs_mu lhgs_h

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

        aa_i       = -cc_i * (invq cc_h)
        bb_i       = -cc_i*dd_h*(invq cc_h) + dd_i

        v_i     = 2^lambda_h * aa_i * (invq $ 2 ^ lambda_i)
        w_i     = (z''_i*2^mu_i + z'_i+aa_i*z''_h*2^mu_h+aa_i*z'_h + bb_i) * (invq $ 2^(lambda_i))


allCoefficients :: [LeakHGS] -> [(Integer, Integer)]
allCoefficients list = map go $ take (h-1) list
    where
        h          = length list
        leak_h     = list !! (h-1)
        go         = getCoefficients leak_h

-- | Verify whether or not a guessed private key corresponds to the real private key. This is done by checking that we indeed solved the discrete logarithm problem,
--   i.e. whether public key indeed equals g^private
verifyCorrectPrivateKey :: Integer -> Integer -> Integer -> Integer -> Bool
verifyCorrectPrivateKey public g p private = public == modexp g private p

-- | Generate a list of random integers between some bounds (lowerBound <= x < upperBound)
randomList :: CryptoRandomGen g => g -> Integer -> Integer -> Int -> IO [Integer]
randomList rng lowerBound upperBound count
    | lowerBound == upperBound = return $ replicate count lowerBound -- There is no randomness in here...
    | otherwise                = flip MS.evalStateT rng $ replicateM count $ do
        let m = upperBound - lowerBound
        r <- MS.get
        case generateMax r m of
                Left err      -> error "Oops"
                Right (k, r') -> MS.put r' >> (return $ lowerBound + k)

mmain = do
    let m        = 2^1024
        nrSigs   = 4
        -- The number of bits leaked can differ each measurement
        minBitLow  = 0
        minBitHigh = 5
        maxBitLow  = 100
        maxBitHigh = 105

    -- Generate some random parameters
    (p, g, q, public, alphaPrivate) <- DSA.parameters m
    rnd                             <- newGenIO :: IO SystemRandom
    leaks                           <- flip MS.evalStateT rnd $ replicateM nrSigs $ DSA.randomSignature p g q alphaPrivate m

    -- TODO, don't reuse rnd!!
    lowerLeakBits <- ZipList <$> randomList rnd minBitLow minBitHigh nrSigs
    upperLeakBits <- ZipList <$> randomList rnd maxBitLow maxBitHigh nrSigs

    let len        = length leaks
        h          = leaks !! (len - 1)
        m_h        = l_message h
        (r_h, s_h) = l_signature h

    let leaked  = getZipList $ (ZipList $ replicate nrSigs leak_hgs) <*> lowerLeakBits <*> upperLeakBits <*> ZipList leaks
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

    putStrLn $ "private key should be: " ++ show alphaPrivate
    putStrLn $ "And we compute it as:  " ++ show computed
    putStrLn $ "Did we correctly solve the DLP? " ++ (show $ verifyCorrectPrivateKey public g p computed)
    putStrLn $ "Difference: " ++ show (alphaPrivate - computed)

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



------
-- Code to display the computations to find the private key using the (unknown) z_h
------

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

------
-- Code to compute the vectors that can be copy-pasted into C++ NTL code
------

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
