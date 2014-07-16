{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Network.Haskoin.Script.Tests (tests) where

import System.TimeIt (timeItT)

import Debug.Trace (traceM)

import Test.QuickCheck
import Test.QuickCheck.Property (Property, (==>))
import qualified Test.QuickCheck.Monadic as QM (monadicIO, PropertyM, assert, run)
import Test.Framework (Test, testGroup, buildTest)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)

import Test.Framework.Runners.Console (defaultMainWithArgs)

import qualified Test.HUnit as HUnit

import Network.BitcoinRPC

import Control.Applicative ((<$>), (<*>))

import Numeric (readHex)

import Control.Lens

import qualified Data.Aeson as A
import qualified Data.Aeson.Lens as AL
import qualified Data.Aeson.Types as AT

import Data.Bits (setBit, testBit)
import Text.Read (readMaybe)
import Data.List (isPrefixOf)
import Data.Char (ord)
import qualified Data.ByteString as BS
    ( singleton
    , length
    , tail
    , head
    , pack
    )

import qualified Data.ByteString.Lazy as LBS
    ( ByteString
    , concat
    , pack
    , unpack
    , toStrict
    )

import Data.Maybe (catMaybes, fromMaybe)

import Data.Binary
    ( Binary
    , Word8
    , encode
    , decode
    , decodeOrFail
    )

import qualified Data.ByteString.Lazy.Char8 as C (readFile)

import Data.Int (Int64)

import Network.Haskoin.Protocol.Arbitrary ()
import Network.Haskoin.Script.Arbitrary

import Network.Haskoin.Script
import Network.Haskoin.Script.Evaluator
import Network.Haskoin.Crypto
import Network.Haskoin.Protocol
import Network.Haskoin.Util

import Control.Monad

import qualified Data.Map as M

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
    , testFile "Canonical Valid Script Test Cases"
               "tests/data/script_valid.json"
               True
    , testFile "Canonical Invalid Script Test Cases"
               "tests/data/script_invalid.json"
               False
    , testGroup "Compare Haskoin Impl against Bitcoin Impl"
        [ testProperty "Haskoin evalScript == Bitcoin evalScript"
                       testCompareScript
        ]
    ]

metaGetPut :: (Binary a, Eq a) => a -> Bool
metaGetPut x = (decode' . encode') x == x

{- Script Parser -}

testScriptOpInt :: ScriptOpInt -> Bool
testScriptOpInt (ScriptOpInt i) = (intToScriptOp <$> scriptOpToInt i) == Right i

testScriptOutput :: ScriptOutput -> Bool
testScriptOutput so = (decodeOutput $ encodeOutput so) == Right so

testScriptInput :: ScriptInput -> Bool
testScriptInput si = (decodeInput $ encodeInput si) == Right si

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

rejectSignature :: SigCheck
rejectSignature _ _ _ = False

evalScript' :: Script -> Script -> Bool
evalScript' sig pubKey = evalScript sig pubKey rejectSignature

execScript' :: Script -> Script -> Either EvalError Program
execScript' sig pubKey = execScript sig pubKey rejectSignature

{- Parse tests from bitcoin-qt repository -}

type ParseError = String
type EncodedScript = LBS.ByteString
data TestData = TestData EncodedScript EncodedScript String
type TestParseResult = Either ParseError TestData

parseHex' :: String -> Maybe [Word8]
parseHex' (a:b:xs) = case readHex $ [a, b] :: [(Integer, String)] of
                      [(i, "")] -> case parseHex' xs of
                                    Just ops -> Just $ fromIntegral i:ops
                                    Nothing -> Nothing
                      _ -> Nothing
parseHex' [_] = Nothing
parseHex' [] = Just []

decodeScript :: LBS.ByteString -> Either ParseError Script
decodeScript bytes = case decodeOrFail bytes of
    Left (_, _, error) -> Left $ "decode error: " ++ error
    Right (_, _, script) -> Right script

parseScript :: String -> Either ParseError EncodedScript
parseScript script =
    do  bytes <- LBS.concat <$> mapM parseToken (words script)
        -- script <- decodeScript bytes
        -- when (encode script /= bytes) $ Left "encode . decode bytes /= bytes"
        return bytes
    where parseToken :: String -> Either ParseError EncodedScript
          parseToken tok =
              case alternatives of
                    (ops:_) -> Right ops
                    _ -> Left $ "unknown token " ++ tok
              where alternatives :: [EncodedScript]
                    alternatives = catMaybes  [ parseHex
                                              , parseInt
                                              , parseQuote
                                              , parseOp
                                              ]
                    parseHex | "0x" `isPrefixOf` tok =
                                    LBS.pack <$> parseHex' (drop 2 tok)
                             | otherwise = Nothing
                    parseInt = fromInt . fromIntegral <$>
                               (readMaybe tok :: Maybe Integer)
                    parseQuote | tok == "''" = Just $ LBS.pack [0]
                               | head tok == '\'' && last tok == '\'' =
                                 Just $ encode $ opPushData $ BS.pack
                                      $ map (fromIntegral . ord)
                                      $ init . tail $ tok
                               | otherwise = Nothing
                    fromInt :: Int64 -> EncodedScript
                    fromInt n | n ==  0 = LBS.pack [0x00]
                              | n == -1 = LBS.pack [0x4f]
                              | 1 <= n &&
                                n <= 16 = LBS.pack [0x50 + fromIntegral n]
                              | otherwise = encode $ opPushData $ BS.pack
                                                   $ encodeInt n
                    parseOp = encode <$>
                              (readMaybe ("OP_" ++ tok) :: Maybe ScriptOp)


getExecError :: (Script -> Script -> String)
getExecError sig key = case execScript' sig key of
                            Left e -> show e
                            Right _ -> "none"


readTests :: String -> IO [TestParseResult]
readTests path = do
    dat <- C.readFile path
    case A.decode dat :: Maybe [[String]] of
        Nothing -> fail "can't parse JSON"
        Just testDefs -> return $ map parseTest testDefs

    where   parseTest :: [String] -> TestParseResult
            parseTest (sig:pubKey:[])       = makeTest "" sig pubKey
            parseTest (sig:pubKey:label:[]) = makeTest label sig pubKey
            parseTest v = fail $ "unknown test format" ++ show v

            makeTest :: String -> String -> String -> TestParseResult
            makeTest comment sig pubKey =
                case (parseScript sig, parseScript pubKey) of
                    (Left e, _) -> Left $ "parse error: sig: " ++ e
                    (_, Left e) -> Left $ "parse error: pubKey: " ++ e
                    (Right sig, Right pubKey) -> Right $ TestData sig pubKey label

                where label = "sig: [" ++ sig ++ "] " ++
                               " pubKey: [" ++ pubKey ++ "] " ++
                               (if null label
                                    then ""
                                    else " comment: " ++ comment)


execFileTests :: String -- ^ group label
              -> String -- ^ path
              -> (TestParseResult -> Test) -- ^ single test function
              -> Test   -- ^ test result

execFileTests groupLabel path runTest = buildTest $ do
    tests <- readTests path
    return $ testGroup groupLabel $ map runTest tests

makeHaskoinEvalTest :: Bool -> TestParseResult -> Test
makeHaskoinEvalTest expected (Left e) =
  testCase e $ HUnit.assertBool "parse error where valid exec is expected"
                                (expected == False)
makeHaskoinEvalTest expected (Right (TestData sig pubKey label)) =
  testCase label $ HUnit.assertBool label (expected == evalResult)
  where evalResult = case (decodeScript sig, decodeScript pubKey) of
            (Right scriptSig, Right scriptPubKey) ->
                evalScript' scriptSig scriptPubKey
            _ -> False

testFile :: String -> String -> Bool -> Test
testFile groupLabel path expected =
  execFileTests groupLabel path (makeHaskoinEvalTest expected)

-- repl utils

execScriptIO :: String -> String -> IO ()
execScriptIO sig key = case (parseDecode sig, parseDecode key) of
  (Left e, _) -> print $ "sig parse error: " ++ e
  (_, Left e) -> print $ "key parse error: " ++ e
  (Right scriptSig, Right scriptPubKey) ->
      case execScript' scriptSig scriptPubKey of
          Left e -> putStrLn $ "error " ++ show e
          Right p -> do putStrLn $ "successful execution"
                        putStrLn $ dumpStack $ runStack p
  where parseDecode :: String -> Either ParseError Script
        parseDecode s = (parseScript s) >>= decodeScript

testValid = testFile "Canonical Valid Script Test Cases"
            "tests/data/script_valid.json" True

testInvalid = testFile "Canonical Valid Script Test Cases"
              "tests/data/script_invalid.json" False

runTests :: [Test] -> IO ()
runTests ts = defaultMainWithArgs ts ["--hide-success"]


-- RPC tests
--
-- needs patched bitcoind that supports 'execscript' rpc command

evalRawRPC :: EncodedScript -> EncodedScript -> IO Bool
evalRawRPC sigData pubKeyData =
    callApi rpcAuth "execscript" params >>= traceResponse >>= evalResponse
    where evalResponse (Right (A.Object v)) = return $ parseResponse v
          evalResponse (Right _) = fail "unexpected response type"
          evalResponse (Left error) = fail $ "RPC error: " ++ error
          rpcAuth = RPCAuth "http://127.0.0.1:18332" "bitcoinrpc" "testnet"
          hexSig = bsToHex $ LBS.toStrict sigData
          hexKey = bsToHex $ LBS.toStrict pubKeyData
          params = LBS.toStrict . A.encode $ [hexSig, hexKey]
          parseResponse v = case AT.parse getValue v of
              AT.Success True -> True
              _ -> False
          getValue o = o A..: "valid"
          traceResponse v = do -- putStrLn $ "response: " ++
                               --         (bsToString . LBS.toStrict)
                               --         (A.encode v)
                               return v

evalRpc :: Script -> Script -> IO Bool
evalRpc sig pubKey = evalRawRPC (encode sig) (encode pubKey)

evalRpcString :: String -> String -> IO Bool
evalRpcString sig pubKey =
    case evalRpc <$> (decodeScript =<< parseScript sig)
                 <*> (decodeScript =<< parseScript pubKey) of
        Left error -> fail $ "decode error: " ++ error
        Right result -> result

makeRPCTest :: Bool -> TestParseResult -> Test
makeRPCTest expected (Left error) =
  testCase error $ HUnit.assertBool "parse error" (expected == False)
makeRPCTest expected (Right (TestData sigData pubKeyData comment)) =
  buildTest $ do rpcResult <- evalRawRPC sigData pubKeyData
                 return $ testCase comment $ HUnit.assertBool
                                             "unexpected result"
                                             (rpcResult == expected)


runRPCTests :: IO ()
runRPCTests =
  let label = "RPC tests"
      pathValid = "tests/data/script_valid.json"
      pathInvalid = "tests/data/script_invalid.json"
      rpcTestValid = execFileTests label pathValid (makeRPCTest True)
      rpcTestInvalid = execFileTests label pathInvalid (makeRPCTest False)
  in runTests [rpcTestValid, rpcTestInvalid]


runStaticComparisonTest :: IO ()
runStaticComparisonTest =
  let label = "RPC tests"
      pathValid = "tests/data/script_valid.json"
      pathInvalid = "tests/data/script_invalid.json"

      cmpTest (Right (TestData sig key comment)) =
        buildTest $ do rpcResult <- evalRawRPC sig key
                       evalResult <- evalEncoded sig key
                       return $ testCase comment $
                                HUnit.assertBool "unequal result"
                                (rpcResult == evalResult)
      cmpTest _ = testCase "ignore parse errors" $
                  HUnit.assertBool "ignore parse errors" True

      evalEncoded sig key = case evalScript' <$> decodeScript sig
                                             <*> decodeScript key of
                                 Right result -> return result
                                 Left _ -> return False

      cmpTestValid = execFileTests label pathValid cmpTest
      cmpTestInvalid = execFileTests label pathInvalid cmpTest
  in runTests [cmpTestValid, cmpTestInvalid]


compareEval :: Script -> Script -> IO Bool
compareEval sig pubKey = ((==) (evalScript' sig pubKey)) <$> evalRpc sig pubKey

testCompareScript :: Script -> Script -> Property
testCompareScript sig pubKey =
    QM.monadicIO $ QM.assert =<< (QM.run $ compareEval sig pubKey)


testDeep :: IO ()
testDeep = quickCheckWith (stdArgs { maxSuccess = 10000
                                   , maxDiscardRatio = 10000 })
                          testCompareScript
