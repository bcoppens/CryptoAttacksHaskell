-- | Implementation of DSA that 'leaks' custom information to simulate a side channel
module LeakingCrypto.DSA (
    Signature(..),
    Leakage(..),
    sign,
    parameters,
    doDigest,
    randomSignature
) where

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

parameters max = do
    keyPair <- OpenSSL.generateDSAParametersAndKey 1024 Nothing -- No optional seed needed here
    return  (  OpenSSL.dsaP keyPair, OpenSSL.dsaG keyPair, OpenSSL.dsaQ keyPair, OpenSSL.dsaPublic keyPair, OpenSSL.dsaPrivate keyPair )

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
