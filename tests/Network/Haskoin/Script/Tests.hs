{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
module Network.Haskoin.Script.Tests (tests) where

import Test.QuickCheck.Property (Property, (==>))
import Test.Framework (Test, testGroup, buildTest)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)

import Test.Framework.Runners.Console (defaultMainWithArgs)

import qualified Test.HUnit as HUnit

import Network.BitcoinRPC

import Control.Applicative ((<$>))

import Numeric (readHex)

import Control.Lens

import qualified Data.Aeson as A
import qualified Data.Aeson.Lens as AL
import qualified Data.Aeson.Types as AT

import Data.Bits (setBit, testBit)
import Text.Read (readMaybe)
import Data.Binary (Binary, Word8)
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
    ( pack
    , unpack
    , toStrict
    )

import Data.Maybe (catMaybes, fromMaybe)

import Data.Binary (encode, decodeOrFail)

import qualified Data.ByteString.Lazy.Char8 as C (readFile)

import Data.Int (Int64)

import Network.Haskoin.Protocol.Arbitrary ()
import Network.Haskoin.Script.Arbitrary

import Network.Haskoin.Script
import Network.Haskoin.Script.Evaluator
import Network.Haskoin.Crypto
import Network.Haskoin.Protocol
import Network.Haskoin.Util


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

{- Parse tests from bitcoin-qt repository -}

type ParseError = String

parseHex' :: String -> Maybe [Word8]
parseHex' (a:b:xs) = case readHex $ [a, b] :: [(Integer, String)] of
                      [(i, "")] -> case parseHex' xs of
                                    Just ops -> Just $ fromIntegral i:ops
                                    Nothing -> Nothing
                      _ -> Nothing
parseHex' [_] = Nothing
parseHex' [] = Just []

parseScript :: String -> Either ParseError Script
parseScript script =
      case parseBytes of
          Left e -> Left $ "string decode error: " ++ e
          Right bytes -> case decodeOrFail $ LBS.pack bytes of
              Left  (_, _, e) -> Left $ "byte decode error: " ++ e ++
                                        "bytes: " ++ (bsToHex $ BS.pack bytes)
              Right (_, _, Script s) -> Right Script { scriptOps = s }
      where
          parseBytes :: Either ParseError [Word8]
          parseBytes = concat <$> mapM parseToken (words script)
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
                    parseInt = fromInt . fromIntegral <$>
                               (readMaybe tok :: Maybe Integer)
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

getExecError :: (Script -> Script -> SigCheck -> String)
getExecError sig key sigCheck =
  case execScript sig key sigCheck of
      Left e -> show e
      Right _ -> "none"


readTests :: String -- ^ path
          -> IO [(Script, Script, String)] -- ^ pairs of (sig, pubKey, comment)
readTests path = do
    dat <- C.readFile path
    case (A.decode dat) :: Maybe [[String]] of
        Nothing -> fail "can't parse JSON"
        Just testDefs -> sequence $ map parseTest testDefs

    where   parseTest :: [String] -> IO (Script, Script, String)
            parseTest (sig:pubKey:[])       = makeTest "" sig pubKey
            parseTest (sig:pubKey:label:[]) = makeTest label sig pubKey
            parseTest v = fail $ "unknown test format" ++ (show v)

            makeTest :: String -> String -> String -> IO (Script, Script, String)
            makeTest comment sig pubKey =
                case (parseScript sig, parseScript pubKey) of
                    (Left e, _) -> fail $ label ++ " can't parse sig: " ++
                                          show sig ++ " error: " ++ e
                    (_, Left e) -> fail $ label ++ "can't parse key: " ++
                                          show pubKey ++ " error: " ++ e
                    (Right scriptSig, Right scriptPubKey) ->
                        return $ (scriptSig, scriptPubKey, label)

                where label = "sig: [" ++ sig ++ "] " ++
                               " pubKey: [" ++ pubKey ++ "] " ++
                               (if null label
                                    then ""
                                    else " comment: " ++ comment)


execFileTests :: String -- ^ group label
              -> String -- ^ path
              -> (Script -> Script -> String -> Test) -- ^ single test function
              -> Test   -- ^ test result

execFileTests groupLabel path makeTest = buildTest $ do
    tests <- readTests path
    return $ testGroup groupLabel $ map makeTest' tests
    where makeTest' (sig, pubKey, comment) = makeTest sig pubKey comment

makeHaskoinEvalTest :: Bool -> Script -> Script -> String -> Test
makeHaskoinEvalTest expected sig pubKey label = testCase label $
  HUnit.assertBool label (expected == evalScript sig pubKey rejectSignature)

testFile :: String -> String -> Bool -> Test
testFile groupLabel path expected =
  execFileTests groupLabel path (makeHaskoinEvalTest expected)

-- repl utils

execScriptIO :: String -> String -> IO ()
execScriptIO sig key = case (parseScript sig, parseScript key) of
  (Left e, _) -> print $ "sig parse error: " ++ e
  (_, Left e) -> print $ "key parse error: " ++ e
  (Right scriptSig, Right scriptPubKey) ->
      case execScript scriptSig scriptPubKey rejectSignature of
          Left e -> putStrLn $ "error " ++ show e
          Right p -> do putStrLn $ "successful execution"
                        putStrLn $ dumpStack $ runStack p


testValid = testFile "Canonical Valid Script Test Cases"
            "tests/data/script_valid.json" True

testInvalid = testFile "Canonical Valid Script Test Cases"
              "tests/data/script_invalid.json" False

runTests :: [Test] -> IO ()
runTests ts = defaultMainWithArgs ts ["--hide-success"]


-- RPC tests
--
-- needs patched bitcoind that supports 'execscript' rpc command

class (A.ToJSON a, A.FromJSON e) => RPCRequest a e r | a -> e, a -> r
  where
    -- | Parse result field in response given corresponding request.
    parseRPCResult :: a -> AT.Value -> AT.Parser r

    -- | Parse error field of response given corresponding request.
    parseRPCError :: a -> AT.Value -> AT.Parser e

    -- | Parse response using request.
    parseRPCResponse :: a -> AT.Value -> AT.Parser (Either e r, Int)
    parseRPCResponse a = AT.withObject "response" $ \o -> do
        i <- o AT..: "id"
        o AT..:? "error" AT..!= AT.Null >>= \e -> case e of
            AT.Null -> o AT..: "result" >>= \r -> do
                res <- parseRPCResult a r
                return (Right res, i)
            _ -> do
                err <- parseRPCError a e
                return (Left err, i)


makeRPCTest :: Bool -> Script -> Script -> String -> Test
makeRPCTest expected scriptSig scriptPubKey comment = buildTest $
    do putStrLn $ "makeRPCTest: " ++ comment ++
                  "\n    hex sig: " ++ hexSig ++
                  "\n    hex key: " ++ hexKey
       res <- callApi rpcAuth "execscript" params
       case res of
           Right (A.Object v) ->
               do putStrLn $ "response: " ++ show v
                  return $ testCase comment
                         $ HUnit.assertBool
                           "eval error" (expected == parseResponse v)
           Right _ -> return $ testCase comment
                             $ HUnit.assertBool "unexpected parse result" False
           Left error -> do putStrLn $ "rpc error: " ++ error
                            return $ testCase comment
                                   $ HUnit.assertBool
                                     ("rpc error: " ++ show error) False
    where
        rpcAuth = RPCAuth "http://127.0.0.1:18332" "bitcoinrpc" "testnet"
        toHex s = bsToHex $ encode' $ Script s
        hexSig = toHex $ scriptOps scriptSig
        hexKey = toHex $ scriptOps scriptPubKey
        params = LBS.toStrict . A.encode $ [hexSig, hexKey]
        parseResponse v = case AT.parse getValue v of
          AT.Success True -> True
          _ -> False
        getValue o = o A..: "valid"

runRPCTests :: IO ()
runRPCTests =
  let label = "RPC tests"
      path = "tests/data/script_valid.json"
      rpcTest = execFileTests label path (makeRPCTest True)
  in runTests [rpcTest]
