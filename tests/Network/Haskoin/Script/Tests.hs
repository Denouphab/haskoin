{-# LANGUAGE OverloadedStrings #-}
module Network.Haskoin.Script.Tests (tests) where

import Test.QuickCheck.Property (Property, (==>))
import Test.Framework (Test, testGroup, buildTest)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)

import Test.Framework.Runners.Console (defaultMainWithArgs)

import qualified Test.HUnit as HUnit

import Control.Applicative ((<$>), (<*>))

import Numeric (showHex, readHex)

import qualified Data.Aeson as A (decode)
import Data.Bits (setBit, testBit)
import Text.Read (readMaybe)
import Data.Binary (Binary, Word8)
import Data.List.Split (splitOn)
import Data.List (isPrefixOf, isSuffixOf, intercalate, intersect)
import Data.Char (ord)
import qualified Data.ByteString as BS
    ( ByteString
    , singleton
    , length
    , tail
    , head
    , pack
    , unpack
    )

import qualified Data.ByteString.Builder as BSB
    ( toLazyByteString
    , byteStringHex
    , word8
    )

import qualified Data.ByteString.Lazy as LBS 
    ( ByteString
    , singleton
    , pack
    , unpack
    )

import Data.Maybe (catMaybes)

import Data.Binary (encode, decode, decodeOrFail)

import qualified Data.ByteString.Lazy.Char8 as C

import Data.Int (Int64)

import Network.Haskoin.Protocol.Arbitrary ()
import Network.Haskoin.Script.Arbitrary 

import Network.Haskoin.Script
import Network.Haskoin.Script.Evaluator
import Network.Haskoin.Script.Types
import Network.Haskoin.Crypto
import Network.Haskoin.Protocol
import Network.Haskoin.Util


tests :: [Test]
tests = 
    [ testGroup "Script types"
        [ testProperty "ScriptOp" (metaGetPut :: ScriptOp -> Bool)
        , testProperty "Script" (metaGetPut :: Script -> Bool)
        ]
    , testGroup "Script Parser"
        [ testProperty "decode . encode OP_1 .. OP_16" testScriptOpInt
        , testProperty "decode . encode ScriptOutput" testScriptOutput
        , testProperty "decode . encode ScriptInput" testScriptInput
        , testProperty "sorting MultiSig scripts" testSortMulSig
        ]
    , testGroup "Script SigHash"
        [ testProperty "canonical signatures" testCanonicalSig
        , testProperty "decode . encode SigHash" binSigHash
        , testProperty "decode SigHash from Word8" binSigHashByte
        , testProperty "encodeSigHash32 is 4 bytes long" testEncodeSH32
        , testProperty "decode . encode TxSignature" binTxSig
        , testProperty "decodeCanonical . encode TxSignature" binTxSigCanonical
        , testProperty "Testing txSigHash with SigSingle" testSigHashOne
        ]
    , testGroup "Integer Types"
        [ testProperty "decodeInt . encodeInt Int"  testEncodeInt
        , testProperty "decodeBool . encodeBool Bool" testEncodeBool
        ]
    {-
    , testGroup "Script Evaluator"
        [ testProperty "OP_DUP"
            (testStackEqual [OP_3, OP_DUP] [[3], [3]])
        , testProperty "OP_IF then"
            (testStackEqual [OP_1, OP_IF, OP_2, OP_ELSE, OP_3, OP_ENDIF] [[2]])
        , testProperty "OP_IF else"
            (testStackEqual [OP_0, OP_IF, OP_2, OP_ELSE, OP_3, OP_ENDIF] [[3]])
        ]

    , testFile "Canonical Valid Script Test Cases"
               "tests/data/script_valid.json"
               True

    , testFile "Canonical Invalid Script Test Cases"
               "tests/data/script_valid.json"
               False
    -}
    ]

metaGetPut :: (Binary a, Eq a) => a -> Bool
metaGetPut x = (decode' . encode') x == x

{- Script Parser -}

testScriptOpInt :: ScriptOpInt -> Bool
testScriptOpInt (ScriptOpInt i) = (intToScriptOp <$> scriptOpToInt i) == Right i

testScriptOutput :: ScriptOutput -> Bool
testScriptOutput so = (decodeOutput $ encodeOutput so) == Right so

testScriptInput :: ScriptPair -> Bool
testScriptInput (ScriptPair si so) = 
    (decodeInput so $ encodeInput si) == Right si

testSortMulSig :: ScriptOutput -> Bool
testSortMulSig out = case out of
    (PayMulSig _ _) -> check $ sortMulSig out
    _ -> True
    where check (PayMulSig ps _)
              | length ps <= 1 = True
              | otherwise = snd $ foldl f (head ps,True) $ tail ps
          check _ = False
          f (a,t) b | t && encode' a <= encode' b = (b,True)
                    | otherwise   = (b,False)

{- Script SigHash -}

testCanonicalSig :: TxSignature -> Bool
testCanonicalSig ts@(TxSignature _ sh) 
    | isSigUnknown sh = isLeft $ decodeCanonicalSig bs
    | otherwise       = isRight (decodeCanonicalSig bs) && 
                        isCanonicalHalfOrder (txSignature ts)
    where bs = encodeSig ts

binSigHash :: SigHash -> Bool
binSigHash sh = (decode' $ encode' sh) == sh

binSigHashByte :: Word8 -> Bool
binSigHashByte w
    | w == 0x01 = res == SigAll False
    | w == 0x02 = res == SigNone False
    | w == 0x03 = res == SigSingle False
    | w == 0x81 = res == SigAll True
    | w == 0x82 = res == SigNone True
    | w == 0x83 = res == SigSingle True
    | testBit w 7 = res == SigUnknown True w
    | otherwise = res == SigUnknown False w
    where res = decode' $ BS.singleton w

testEncodeSH32 :: SigHash -> Bool
testEncodeSH32 sh = BS.length bs == 4 && BS.head bs == w && BS.tail bs == zs
    where bs = encodeSigHash32 sh
          w  = BS.head $ encode' sh
          zs = BS.pack [0,0,0]

binTxSig :: TxSignature -> Bool
binTxSig ts = (fromRight $ decodeSig $ encodeSig ts) == ts

binTxSigCanonical :: TxSignature -> Bool
binTxSigCanonical ts@(TxSignature _ sh) 
    | isSigUnknown sh = isLeft $ decodeCanonicalSig $ encodeSig ts
    | otherwise = (fromRight $ decodeCanonicalSig $ encodeSig ts) == ts

testSigHashOne :: Tx -> Script -> Bool -> Property
testSigHashOne tx s acp = not (null $ txIn tx) ==> 
    if length (txIn tx) > length (txOut tx) 
        then res == (setBit 0 248)
        else res /= (setBit 0 248)
    where res = txSigHash tx s (length (txIn tx) - 1) (SigSingle acp)



{- Script Evaluation Primitives -}

testEncodeInt :: Int64 -> Bool
testEncodeInt i = (decodeInt $ encodeInt i) == i

testEncodeBool :: Bool -> Bool
testEncodeBool b = (decodeBool $ encodeBool b) == b

{- Script Evaluation -}

emptyScript :: Script
emptyScript = Script { scriptOps = [] }

rejectSignature :: SigCheck
rejectSignature _ _ _ = False

{-
testStackEqual :: [ScriptOp] -> Stack -> Bool
testStackEqual scriptOps result =
    case get <$> evalAll scriptOps of
        Left _ -> False
        Right p -> True

-}

{- Parse tests from bitcoin-qt repository -}

type ParseError = String

decodeByte :: Word8 -> Maybe ScriptOp
decodeByte = decode . LBS.singleton

parseHex' :: String -> Maybe [Word8]
parseHex' (a:b:xs) = case readHex $ a:b:[] of
                      [(i, "")] -> case parseHex' xs of
                                    -- Just ops -> Just $ ops ++ [fromIntegral i]
                                    Just ops -> Just $ fromIntegral i:ops
                                    Nothing -> Nothing
                      _ -> Nothing
parseHex' [_] = Nothing
parseHex' [] = Just []

parseScript :: String -> Either ParseError Script
parseScript "" = Right emptyScript
parseScript script =
      case LBS.pack <$> bytes of
          Left e -> Left $ "string decode error: " ++ e
          Right bytes -> case decodeOrFail bytes of
              Left  (_, _, e) -> Left $ "byte decode error: " ++ e ++
                                        "bytes: " ++ (show bytes)
              Right (_, _, s) -> Right $ Script { scriptOps =  s }
      where
          bytes = concat <$> (sequence $ map parseToken $ words script)
          parseToken :: String -> Either ParseError [Word8]
          parseToken tok =
              case alternatives of
                    (ops:_) -> Right ops
                    _ -> Left $ "unknown token " ++ tok
              where alternatives :: [[Word8]]
                    alternatives = catMaybes  [ parseHex
                                              , parseInt
                                              , parseQuote
                                              , parseOp
                                              ]
                    parseHex | "0x" `isPrefixOf` tok = parseHex' (drop 2 tok)
                             | otherwise = Nothing
                    parseInt = fromInt . fromIntegral <$> (readMaybe tok)
                    parseQuote | tok == "''" = Just [0]
                               | (head tok) == '\'' && (last tok) == '\'' =
                                 Just $ encodeBytes $ opPushData $ BS.pack
                                      $ map (fromIntegral . ord)
                                      $ init . tail $ tok
                               | otherwise = Nothing
                    fromInt :: Int64 -> [Word8]
                    fromInt n | n ==  0 = [0x00]
                              | n == -1 = [0x4f]
                              | 1 <= n && n <= 16 = [0x50 + fromIntegral n]
                              | otherwise = encodeBytes
                                                $ opPushData $ BS.pack
                                                $ encodeInt n
                    parseOp = encodeBytes <$> (readMaybe $ "OP_" ++ tok)
                    encodeBytes = LBS.unpack . encode

testFile :: String -> String -> Bool -> Test
testFile label path expected = buildTest $ do
    dat <- C.readFile path
    case (A.decode dat) :: Maybe [[String]] of
        Nothing -> return $
                    testCase label $
                    HUnit.assertFailure $ "can't read test file " ++ path
        Just tests -> return $ testGroup label $ map parseTest tests

    where   parseTest :: [String] -> Test
            parseTest (sig:pubKey:[])       = makeTest "" sig pubKey
            parseTest (sig:pubKey:label:[]) = makeTest label sig pubKey

            parseTest v =
                testCase "can't parse test case" $
                         HUnit.assertFailure $ "json element " ++ show v

            makeTest :: String -> String -> String -> Test
            makeTest label sig pubKey =
                testCase label' $ case (parseScript sig, parseScript pubKey) of
                    (Left e, _) -> fail $ "can't parse sig: " ++ show sig
                                          ++ " error: " ++ e
                    (_, Left e) -> fail $ "can't parse key: " ++ show pubKey
                                          ++ " error: " ++ e
                    (Right scriptSig, Right scriptPubKey) ->
                        check $ execScript scriptSig scriptPubKey rejectSignature
                        where check (Left err) =
                                  HUnit.assertFailure $ "error: " ++ show err
                              check (Right p) =
                                  let x = checkStack . runStack $ p
                                  in HUnit.assertBool
                                     ("unexpected eval result: " ++ (show x))
                                     (expected == x)

                    where label' = "sig: [" ++ sig ++ "] " ++
                                   " pubKey: [" ++ pubKey ++ "] " ++
                                   (if null label
                                        then ""
                                        else " label: " ++ label)

execScriptIO :: String -> IO ()
execScriptIO s = case parseScript s of
  Left e -> print $ "parse error: " ++ e
  Right s -> case execScript emptyScript s rejectSignature of
                  Left e -> putStrLn $ "error " ++ show e
                  Right p -> do putStrLn $ "successful execution"
                                putStrLn $ dumpStack $ runStack p


testValid = testFile "Canonical Valid Script Test Cases"
            "tests/data/script_valid.json" True

testInvalid = testFile "Canonical Valid Script Test Cases"
              "tests/data/script_invalid.json" False

runTest = defaultMainWithArgs [testValid] ["--hide-success"]
