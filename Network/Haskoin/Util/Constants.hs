{-|
  Declaration of constants used across the bitcoin protocol.
-}
module Network.Haskoin.Util.Constants where

import Data.Word (Word8,Word32)

-- | Prefix for base58 PubKey hash address
addrPrefix :: Word8
addrPrefix = 0

-- | Prefix for base58 script hash address
scriptPrefix :: Word8
scriptPrefix = 5

-- | Prefix for private key WIF format
secretPrefix :: Word8
secretPrefix = 128

-- | Prefix for extended public keys (BIP32)
extPubKeyPrefix :: Word32
extPubKeyPrefix = 0x0488b21e

-- | Prefix for extended private keys (BIP32)
extSecretPrefix :: Word32
extSecretPrefix = 0x0488ade4

-- | Network magic bytes
networkMagic :: Word32
networkMagic = 0xf9beb4d9 

-- | Genesis block header information
genesisHeader :: [Integer]
genesisHeader =
    -- Hash = 000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f
    [ 0x01
    , 0x00
    , 0x3ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a
    , 1231006505
    , 486604799
    , 2083236893
    ]

-- | Maximum size of a block in bytes
maxBlockSize :: Int
maxBlockSize = 1000000

-- | User agent of this haskoin package
haskoinUserAgent :: String
haskoinUserAgent = "/haskoin:0.0.2.1/"

