module GenForeign (genForeign) where

import Error(internalError, ErrMsg(..), ErrorHandle, bsError)
import Util(headOrErr, findSame)
import Flags
import Pragma
import Id
import CSyntax
import PPrint
import ABin (ABin(..), ABinForeignFuncInfo(..))
import GenABin(genABinFile)
import ForeignFunctions(ForeignFunction(..), mkForeignFunction)
import Version(bscVersionStr)
import FileNameUtil(mkAName, getRelativeFilePath)
import TopUtils(putStrLnF)

import Control.Monad(unless)

-- For dumping purposes, this returns a list of
-- the foreign src IDs, and their corresponding ForeignFunctions
genForeign :: ErrorHandle -> Flags -> String -> CPackage ->
              IO [(Id, ForeignFunction)]
genForeign errh flags prefix (CPackage pkg_id _ _ _ _ defs _) =
    let
        isPPforeignImport (PPforeignImport {}) = True
        isPPforeignImport _ = False

        foreignIds = [ i | (CPragma (Pproperties i pps)) <- defs,
                           any isPPforeignImport pps ]
        foreignDefs = [ d | d@(CValueSign (CDefT i _ _ _)) <- defs,
                            i `elem` foreignIds ]
        foreignInfos = map extractForeignFuncInfo foreignDefs

        genABin info@(src_id, foreign_func) =
            let ffinfo = ABinForeignFuncInfo src_id foreign_func
                abin = ABinForeignFunc ffinfo (bscVersionStr True)
                -- generate the filename
                afilename_base = getIdString (ff_name foreign_func)
                afilename = mkAName (bdir flags) prefix afilename_base
                afilename_rel = getRelativeFilePath afilename
                -- user message
                abinPrintPrefix = "Foreign import file created: "
            in  do
                   -- write the file with full path
                   genABinFile errh afilename abin
                   -- report the file to the user with relative path
                   -- (typically just the filename, for current directory)
                   unless (quiet flags) $ putStrLnF $ abinPrintPrefix ++ afilename_rel
                   -- return the info, for dumping
                   return info

        -- check for duplicate imports and report an error
        link_ids = map (ff_name . snd) foreignInfos
        duplicates = findSame link_ids
        mkDupErr dups =
            let link_id = headOrErr "GenForeign mkDupErr link" dups
                has_this_link (i,ff) = (ff_name ff == link_id)
                src_ids = map fst (filter has_this_link foreignInfos)
                src_ips = map (\i -> (getIdString i, getPosition i)) src_ids
                link_name = getIdString link_id
                pos = getPosition link_id
            in  (pos, EForeignFuncDuplicates link_name src_ips)
    in
        if (not (null duplicates))
        then bsError errh (map mkDupErr duplicates)
        else mapM genABin foreignInfos


-- After typechecking, the import should contain a CForeignFuncCT expression
-- which contains the primitive type.  This function extracts that.
extractForeignFuncInfo :: CDefn -> (Id, ForeignFunction)
extractForeignFuncInfo defn =
    let
        extractFromCDefn (CValueSign (CDefT _ _ _ clauses)) =
            concatMap extractFromCClause clauses
        extractFromCDefn _ = internalError "GenForeign: extractFromCDefn"

        extractFromCClause (CClause _ _ expr) = extractFromCExpr expr

        extractFromCExpr expr@(CForeignFuncCT {}) = [expr]
        extractFromCExpr (CLam _ expr) = extractFromCExpr expr
        extractFromCExpr (CLamT _ _ expr) = extractFromCExpr expr
        extractFromCExpr (Cletseq defs expr) =
            concatMap extractFromCDefl defs ++ extractFromCExpr expr
        extractFromCExpr (Cletrec defs expr) =
            concatMap extractFromCDefl defs ++ extractFromCExpr expr
        extractFromCExpr (CApply expr1 exprs) =
            extractFromCExpr expr1 ++ concatMap extractFromCExpr exprs
        extractFromCExpr _ = []

        extractFromCDefl (CLValueSign (CDefT _ _ _ clauses) _) =
            concatMap extractFromCClause clauses
        extractFromCDefl _ = internalError "GenForeign: extractFromCDefl"

    in
        case (extractFromCDefn defn) of
            [CForeignFuncCT link_id ctype] ->
                case (getName defn) of
                  Right i -> (i, mkForeignFunction link_id ctype)
                  Left _ -> internalError "GenForeign: getName"
            res -> internalError ("GenForeign: foreigns = " ++
                                  ppReadable res)
