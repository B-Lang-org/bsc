-- Direct tests of the production analysis, including ambiguous wire names
-- that cannot be expressed through ordinary source-level port declarations.
-- See run.sh for the correctness and optional scaling commands.
module Main where

import Control.DeepSeq(force)
import Control.Exception(evaluate)
import Control.Monad(unless)
import qualified Data.Map as M
import System.CPUTime(getCPUTime)
import System.Environment(getArgs)
import Text.Printf(printf)
import Text.Read(readMaybe)

import ASyntax
import Id(mk_homeless_id)
import ISyntax(IType)
import ISyntaxUtil(itBool, itBitN)
import SchedInfo(SchedInfo(..), MethodConflictInfo(..))
import VModInfo
import WireAnalysis(getWireTypeMap)

clocks :: VClockInfo
clocks = ClockInfo [] [] [] []

resets :: VResetInfo
resets = ResetInfo [] []

package :: [(String, IType)] -> [AVInst] -> APackage
package external instances = APackage {
    apkg_name = mk_homeless_id "test",
    apkg_is_wrapped = False,
    apkg_backend = Nothing,
    apkg_size_params = [],
    apkg_inputs = [],
    apkg_clock_domains = [],
    apkg_external_wires = WireInfo clocks resets [],
    apkg_external_wire_types = M.fromList [(VName n, t) | (n, t) <- external],
    apkg_reset_list = [],
    apkg_state_instances = instances,
    apkg_local_defs = [],
    apkg_rules = [],
    apkg_schedule_pragmas = [],
    apkg_interface = [],
    apkg_inst_comments = [],
    apkg_inst_tree = M.empty,
    apkg_proof_obligations = []
    }

instanceWithType :: String -> IType -> AVInst
instanceWithType name typ =
    AVInst (mk_homeless_id name) (ATBit 1) False []
        (M.singleton (VName "OUT") typ)
        (mkVModInfo (VName "TestPrimitive") clocks resets [] []
            (SchedInfo (MethodConflictInfo [] [] [] [] [] [] []) [] [] [])
            (VPathInfo [])) [] []

checkPairs :: IO ()
checkPairs = do
    -- The first pair is repeated across external and submodule entries.
    -- The final instance repeats an earlier instance. Bool and Bit#(1)
    -- must both survive under a$OUT and a.OUT, despite their equal width.
    let input = package [("z", itBool), ("a$OUT", itBool)]
            [ instanceWithType "a" itBool,
              instanceWithType "a" (itBitN 1),
              instanceWithType "b" (itBitN 1),
              instanceWithType "a" itBool ]
        expected =
            [ ("a$OUT", itBool), ("z", itBool), ("a.OUT", itBool),
              ("a$OUT", itBitN 1), ("a.OUT", itBitN 1),
              ("b$OUT", itBitN 1), ("b.OUT", itBitN 1) ]
        actual = getWireTypeMap input
    unless (actual == expected) $
        error ("wrong candidate order or deduplication: " ++ show actual)
    unless (null (getWireTypeMap (package [] []))) $
        error "empty package has candidate wires"
    putStrLn "PASS: stable pair deduplication, category order, distinct same-name types"

benchmark :: Int -> IO ()
benchmark count = do
    let input = package []
            [ instanceWithType ("wire" ++ show i) (itBitN 32)
            | i <- [1..count] ]
    -- Exclude package construction; force the entire result inside the
    -- timed interval. This measures analysis, not Tcl/type rendering.
    _ <- evaluate (force input)
    start <- getCPUTime
    result <- evaluate (force (getWireTypeMap input))
    end <- getCPUTime
    unless (length result == 2 * count) $
        error "incorrect benchmark candidate count"
    printf "%d instances, %d entries: %.6f CPU seconds\n"
        count (length result) (fromIntegral (end - start) / 1e12 :: Double)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> checkPairs
        [arg] | Just count <- readMaybe arg, count > 0 -> benchmark count
        _ -> error "usage: WireTypeMapCheck [positive-instance-count]"
