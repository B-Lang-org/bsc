{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Werror -fwarn-incomplete-patterns #-}
module GenBin(genBinFile, readBinFile) where

import Control.Monad(when)
import Data.Word
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as B
import Position
import Pragma
import Error(internalError, ErrMsg(..), ErrorHandle, bsError)
import ISyntax
import ISyntaxUtil(icUndet)
import CSyntax
import Undefined(UndefKind(UNoMatch))
import BinData
import FileIOUtil(writeBinaryFileCatch)
import PFPrint

import Debug.Trace
import IOUtil(progArgs)

doTrace :: Bool
doTrace = elem "-trace-genbin" progArgs

-- .bo file tag -- change this whenever the .bo format changes
-- See also GenABin.header
header :: [Byte]
header = B.unpack $ TE.encodeUtf8 $ T.pack "bsc-bo-20230831-1"

genBinFile :: ErrorHandle ->
              String -> CSignature -> CSignature -> IPackage a -> IO ()
genBinFile errh fn bi_sig bo_sig ipkg =
    writeBinaryFileCatch errh fn (header ++ encode (bi_sig, bo_sig, ipkg))

readBinFile :: ErrorHandle -> String -> [Word8] ->
               IO (CSignature, CSignature, IPackage a, String)
readBinFile errh nm s =
    if take (length header) s == header
    then let ((bi_sig, bo_sig, ipkg), hash) =
                 decodeWithHash $ drop (length header) s
         in return (bi_sig, bo_sig, ipkg, hash)
    else bsError errh [(noPosition, EBinFileVerMismatch nm)]

-- ----------
-- Bin CSignature

instance Bin CSignature where
    writeBytes (CSignature n is fs ds) =
        section "CSignature" $
        do toBin n; toBin is; toBin fs; toBin ds
    readBytes = do when doTrace $ traceM("read CSignature")
                   n  <- fromBin
                   is <- fromBin
                   fs <- fromBin
                   ds <- fromBin
                   return $ CSignature n is fs ds

-- ----------
-- Bin CFixity

instance Bin CFixity where
    writeBytes (CInfix  f i) = do putI 0; toBin f; toBin i
    writeBytes (CInfixl f i) = do putI 1; toBin f; toBin i
    writeBytes (CInfixr f i) = do putI 2; toBin f; toBin i
    readBytes = do when doTrace $ traceM("read CFixity")
                   tag <- getI; f <- fromBin; i <- fromBin
                   case tag of
                     0 -> return $ CInfix  f i
                     1 -> return $ CInfixl f i
                     2 -> return $ CInfixr f i
                     n -> internalError $ "GenBin.Bin(CFixity).readBytes: " ++ show n

-- ----------
-- Bin CDefn

instance Bin CDefn where
    writeBytes (Ctype ik is t) = do putI 0; toBin ik; toBin is; toBin t
    -- drop derivings because we don't derive after reading .bo
    writeBytes (Cdata vis ik vs ocs cs _) =
        do putI 1; toBin vis; toBin ik; toBin vs; toBin ocs; toBin cs
    writeBytes (Cstruct vis st ik is fs _) =
        do putI 2; toBin vis; toBin st; toBin ik; toBin is; toBin fs
    writeBytes (Cclass incoh ps ik is deps fs) =
        do putI 3; toBin incoh; toBin ps; toBin ik; toBin is; toBin deps; toBin fs
    writeBytes (Cforeign n cqt fn ports) =
        do putI 4; toBin n; toBin cqt; toBin fn; toBin ports
    writeBytes (Cprimitive i cqt) = do putI 5; toBin i; toBin cqt
    writeBytes (CprimType ik) = do putI 6; toBin ik
    writeBytes (CIinstance i cqt) = do putI 7; toBin i; toBin cqt
    writeBytes (CIclass incoh ps ik is deps poss) =
        do putI 8; toBin incoh; toBin ps; toBin ik; toBin is; toBin deps; toBin poss
    writeBytes (CIValueSign i cqt) = do putI 9; toBin i; toBin cqt
    writeBytes (CItype ik is poss) = do putI 10; toBin ik; toBin is; toBin poss
    writeBytes (CPragma p) = do putI 11; toBin p
    writeBytes def = internalError $ "GenBin.Bin(CDefn) not supported " ++ ppReadable def
    readBytes = do when doTrace $ traceM ("read CDefn")
                   tag <- getI
                   case tag of
                     0  -> do when doTrace $ traceM ("Ctype")
                              ik <- fromBin; is <- fromBin; t <- fromBin
                              return (Ctype ik is t)
                     1  -> do when doTrace $ traceM ("Cdata")
                              vis <- fromBin
                              ik <- fromBin
                              vs <- fromBin
                              ocs <- fromBin
                              cs <- fromBin
                              return (Cdata vis ik vs ocs cs [])
                     2  -> do when doTrace $ traceM ("Cstruct")
                              vis <- fromBin
                              st <- fromBin
                              ik <- fromBin
                              is <- fromBin
                              fs <- fromBin
                              return (Cstruct vis st ik is fs [])
                     3  -> do when doTrace $ traceM ("Cclass")
                              incoh <- fromBin
                              ps <- fromBin
                              ik <- fromBin
                              is <- fromBin
                              deps <- fromBin
                              fs <- fromBin
                              return (Cclass incoh ps ik is deps fs)
                     4  -> do when doTrace $ traceM ("Cforeign")
                              n <- fromBin
                              cqt <- fromBin
                              fn <- fromBin
                              ports <- fromBin
                              return (Cforeign n cqt fn ports)
                     5  -> do when doTrace $ traceM ("Cprimitive")
                              i <- fromBin; cqt <- fromBin
                              return (Cprimitive i cqt)
                     6  -> do when doTrace $ traceM ("CprimType")
                              ik <- fromBin
                              return (CprimType ik)
                     7  -> do when doTrace $ traceM ("CIinstance")
                              i <- fromBin; cqt <- fromBin
                              return (CIinstance i cqt)
                     8  -> do when doTrace $ traceM ("CIclass")
                              incoh <- fromBin
                              ps <- fromBin
                              ik <- fromBin
                              is <- fromBin
                              deps <- fromBin
                              poss <- fromBin
                              return (CIclass incoh ps ik is deps poss)
                     9  -> do when doTrace $ traceM ("CIValueSign")
                              i <- fromBin; cqt <- fromBin
                              return (CIValueSign i cqt)
                     10 -> do when doTrace $ traceM ("CItype")
                              ik <- fromBin; is <- fromBin; poss <- fromBin
                              return (CItype ik is poss)
                     11 -> do p <- fromBin; return (CPragma p)
                     n  -> internalError $ "GenBin.Bin(CDefn).readBytes: " ++ show n

-- ----------
-- Bin IdK

instance Bin IdK where
    writeBytes (IdK i)       = do putI 0; toBin i
    writeBytes (IdKind i k)  = do putI 1; toBin i; toBin k
    writeBytes (IdPKind i k) =
        internalError $ "GenBin.Bin(IdK).writeBytes: IdPKind"
    readBytes = do when doTrace $ traceM ("read IdK")
                   tag <- getI;
                   case tag of
                     0 -> do i <- fromBin; return (IdK i)
                     1 -> do i <- fromBin; k <- fromBin; return (IdKind i k)
                     n -> internalError $ "GenBin.Bin(IdK).readBytes: " ++ show n

-- ----------
-- Bin CInternalSummand

instance Bin CInternalSummand where
    writeBytes (CInternalSummand is t mn) =
        section "CInternalSummand" $
        do toBin is; toBin t; toBin mn
    readBytes = do when doTrace $ traceM("read CInternalSummand")
                   is <- fromBin; t <- fromBin; mn <- fromBin
                   return (CInternalSummand is t mn)

-- ----------
-- Bin COriginalSummand

instance Bin COriginalSummand where
    writeBytes (COriginalSummand is ts fns mn) =
        section "COriginalSummand" $
        do toBin is; toBin ts; toBin fns; toBin mn
    readBytes = do when doTrace $ traceM("read COriginalSummand")
                   is <- fromBin; ts <- fromBin; fns <- fromBin; mn <- fromBin
                   return (COriginalSummand is ts fns mn)

-- ----------
-- Bin CField

instance Bin CField where
    writeBytes (CField n ps cqt def_cs mot) =
        section "CField" $
        do toBin n; toBin ps; toBin cqt; toBin def_cs; toBin mot
    readBytes = do when doTrace $ traceM ("read CField")
                   n <- fromBin; ps <- fromBin; cqt <- fromBin;
                   def_cs <- fromBin; mot <- fromBin;
                   return (CField n ps cqt def_cs mot)

-- needed by CField defaulting

instance Bin CClause where
    writeBytes (CClause ps qs e) =
        section "CClause" $ do toBin ps; toBin qs; toBin e
    readBytes = do when doTrace $ traceM ("read CClause")
                   ps <- fromBin; qs <- fromBin; e <- fromBin;
                   return (CClause ps qs e)

instance Bin CPat where
    writeBytes (CPCon i ps) = do putI 0; toBin i; toBin ps
    writeBytes (CPstruct mb i ips) = do putI 1; toBin mb; toBin i; toBin ips
    writeBytes (CPVar i) = do putI 2; toBin i
    writeBytes (CPAs i p) = do putI 3; toBin i; toBin p
    writeBytes (CPAny p) = do putI 4; toBin p
    writeBytes (CPLit l) = do putI 5; toBin l
    writeBytes (CPMixedLit pos n ns) = do putI 6; toBin pos; toBin n; toBin ns
    writeBytes (CPOper ops) = do putI 7; toBin ops
    writeBytes (CPCon1 i1 i2 p) = do putI 8; toBin i1; toBin i2; toBin p
    writeBytes (CPConTs i1 i2 ts ps) =
        do putI 9; toBin i1; toBin i2; toBin ts; toBin ps
    readBytes = do tag <- getI
                   case tag of
                     0 -> do i <- fromBin; ps <- fromBin
                             return (CPCon i ps)
                     1 -> do mb <- fromBin; i <- fromBin; ips <- fromBin;
                             return (CPstruct mb i ips)
                     2 -> do i <- fromBin; return (CPVar i)
                     3 -> do i <- fromBin; p <- fromBin; return (CPAs i p)
                     4 -> do p <- fromBin; return (CPAny p)
                     5 -> do l <- fromBin; return (CPLit l)
                     6 -> do pos <- fromBin; n <- fromBin; ns <- fromBin;
                             return (CPMixedLit pos n ns)
                     7 -> do ops <- fromBin; return (CPOper ops)
                     8 -> do i1 <- fromBin; i2 <- fromBin; p <- fromBin;
                             return (CPCon1 i1 i2 p)
                     9 -> do i1 <- fromBin; i2 <- fromBin;
                             ts <- fromBin; ps <- fromBin;
                             return (CPConTs i1 i2 ts ps)
                     n -> internalError $ "GenBin.Bin(CPat).readBytes: " ++ show n

instance Bin CPOp where
    writeBytes (CPRand p) = do putI 0; toBin p
    writeBytes (CPRator n i) = do putI 1; toBin n; toBin i
    readBytes =
        do tag <- getI
           case tag of
             0 -> do p <- fromBin; return (CPRand p)
             1 -> do n <- fromBin; i <- fromBin; return (CPRator n i)
             n -> internalError $ "GenBin.Bin(CPOp).readBytes: " ++ show n

instance Bin COp where
    writeBytes (CRand e) = do putI 0; toBin e
    writeBytes (CRator n i) = do putI 1; toBin n; toBin i
    readBytes =
        do tag <- getI
           case tag of
             0 -> do e <- fromBin; return (CRand e)
             1 -> do n <- fromBin; i <- fromBin; return (CRator n i)
             n -> internalError $ "GenBin.Bin(COp).readBytes: " ++ show n

instance Bin CLiteral where
    writeBytes (CLiteral pos l) = do toBin pos; toBin l
    readBytes = do pos <- fromBin; l <- fromBin; return (CLiteral pos l)

instance Bin Char where
    writeBytes c = writeBytes [c]
    readBytes = do s <- readBytes
                   case s of
                       [c] -> return c
                       _ -> internalError $ "GenBin.Bin(Char).readBytes: bad char: " ++ s

instance Bin Literal where
    writeBytes (LString s) = do putI 0; toBin s
    writeBytes (LChar c)   = do putI 1; toBin c
    writeBytes (LInt il)   = do putI 2; toBin il
    writeBytes (LReal d)   = do putI 3; toBin d
    writeBytes (LPosition) = do putI 4
    readBytes = do tag <- getI
                   case tag of
                     0 -> do s <- fromBin; return (LString s)
                     1 -> do c <- fromBin; return (LChar c)
                     2 -> do il <- fromBin; return (LInt il)
                     3 -> do d <- fromBin; return (LReal d)
                     4 -> return LPosition
                     n -> internalError $ "GenBin.Bin(Literal).readBytes: " ++ show n

instance Bin CQual where
    writeBytes (CQGen t p e) = do putI 0; toBin t; toBin p; toBin e
    writeBytes (CQFilter e)  = do putI 1; toBin e
    readBytes = do tag <- getI
                   case tag of
                     0 -> do t <- fromBin; p <- fromBin; e <- fromBin
                             return (CQGen t p e)
                     1 -> do e <- fromBin; return (CQFilter e)
                     n -> internalError $ "GenBin.Bin(CQual).readBytes: " ++ show n

instance Bin CExpr where
    writeBytes (CLam i e) = do putI 0; toBin i; toBin e
    writeBytes (CLamT i qt e) = do putI 1; toBin i; toBin qt; toBin e
    writeBytes (Cletseq ds e) = do putI 2; toBin ds; toBin e
    writeBytes (Cletrec ds e) = do putI 3; toBin ds; toBin e
    writeBytes (CSelect e i) = do putI 4; toBin e; toBin i
    writeBytes (CCon i es) = do putI 5; toBin i; toBin es
    writeBytes (Ccase pos e arms) = do putI 6; toBin pos; toBin e; toBin arms
    writeBytes (CStruct mb i ies) = do putI 7; toBin mb; toBin i; toBin ies
    writeBytes (CStructUpd e ies) = do putI 8; toBin e; toBin ies
    writeBytes (Cwrite pos e1 e2) = do putI 9; toBin pos; toBin e1; toBin e2
    writeBytes (CAny pos uk) = do putI 10; toBin pos; toBin uk
    writeBytes (CVar i) = do putI 11; toBin i
    writeBytes (CApply e es) = do putI 12; toBin e; toBin es
    writeBytes (CTaskApply e es) = do putI 13; toBin e; toBin es
    writeBytes (CTaskApplyT e t es) = do putI 14; toBin e; toBin t; toBin es
    writeBytes (CLit l) = do putI 15; toBin l
    writeBytes (CBinOp e1 i e2) = do putI 16; toBin e1; toBin i; toBin e2
    writeBytes (CHasType e qt) = do putI 17; toBin e; toBin qt
    writeBytes (Cif pos e1 e2 e3) = do putI 18;
                                       toBin pos; toBin e1; toBin e2; toBin e3
    writeBytes (CSub pos e1 e2) = do putI 19; toBin pos; toBin e1; toBin e2
    writeBytes (CSub2 e1 e2 e3) = do putI 20; toBin e1; toBin e2; toBin e3
    writeBytes (Cmodule pos ss) = do putI 21; toBin pos; toBin ss
    writeBytes (Cinterface pos mi ds) = do putI 22;
                                           toBin pos; toBin mi; toBin ds
    writeBytes (CmoduleVerilog e b vc vr va vf vs vp) =
        do putI 23; toBin e; toBin b; toBin vc; toBin vr; toBin va;
           toBin vf; toBin vs; toBin vp
    writeBytes (CForeignFuncC i qt) = do putI 24; toBin i; toBin qt
    writeBytes (Cdo b ss) = do putI 25; toBin b; toBin ss
    writeBytes (Caction pos ss) = do putI 26; toBin pos; toBin ss
    writeBytes (Crules ps rs) = do putI 27; toBin ps; toBin rs
    writeBytes (COper ops) = do putI 29; toBin ops
    -- these are from deriving and typecheck
    writeBytes (CCon1 i1 i2 e) = do putI 30; toBin i1; toBin i2; toBin e
    writeBytes (CSelectTT i1 e i2) = do putI 31; toBin i1; toBin e; toBin i2
    writeBytes (CCon0 mi i) = do putI 32; toBin mi; toBin i
    writeBytes (CConT i1 i2 es) = do putI 33; toBin i1; toBin i2; toBin es
    writeBytes (CStructT t ies) = do putI 34; toBin t; toBin ies
    writeBytes (CSelectT i1 i2) = do putI 35; toBin i1; toBin i2
    writeBytes (CLitT t l) = do putI 36; toBin t; toBin l
    writeBytes (CAnyT pos uk t) = do putI 37; toBin pos; toBin uk
    writeBytes (CmoduleVerilogT t e b vc vr va vf vs vp) =
        do putI 38; toBin t; toBin e; toBin b; toBin vc; toBin vr; toBin va;
           toBin vf; toBin vs; toBin vp
    writeBytes (CForeignFuncCT i t) = do putI 39; toBin i; toBin t
    writeBytes (CTApply e ts) = do putI 40; toBin e; toBin ts
    writeBytes (Cattributes ps) = do putI 41; toBin ps
    writeBytes (CSubUpdate pos e_vec (e_h, e_l) e_rhs) = do
      putI 42; toBin pos; toBin e_vec; toBin e_h;
      toBin e_l; toBin e_rhs
    readBytes =
        do tag <- getI
           case tag of
             0 -> do i <- fromBin; e <- fromBin; return (CLam i e)
             1 -> do i <- fromBin; qt <- fromBin; e <- fromBin;
                     return (CLamT i qt e)
             2 -> do ds <- fromBin; e <- fromBin; return (Cletseq ds e)
             3 -> do ds <- fromBin; e <- fromBin; return (Cletrec ds e)
             4 -> do e <- fromBin; i <- fromBin; return (CSelect e i)
             5 -> do i <- fromBin; es <- fromBin; return (CCon i es)
             6 -> do pos <- fromBin; e <- fromBin; arms <- fromBin;
                     return (Ccase pos e arms)
             7 -> do mb <- fromBin; i <- fromBin; ies <- fromBin;
                     return (CStruct mb i ies)
             8 -> do i <- fromBin; ies <- fromBin; return (CStructUpd i ies)
             9 -> do pos <- fromBin; e1 <- fromBin; e2 <- fromBin;
                     return (Cwrite pos e1 e2)
             10 -> do pos <- fromBin; uk <- fromBin; return (CAny pos uk)
             11 -> do i <- fromBin; return (CVar i)
             12 -> do e <- fromBin; es <- fromBin; return (CApply e es)
             13 -> do e <- fromBin; es <- fromBin; return (CTaskApply e es)
             14 -> do e <- fromBin; t <- fromBin; es <- fromBin;
                      return (CTaskApplyT e t es)
             15 -> do l <- fromBin; return (CLit l)
             16 -> do e1 <- fromBin; i <- fromBin; e2 <- fromBin;
                      return (CBinOp e1 i e2)
             17 -> do e <- fromBin; qt <- fromBin; return (CHasType e qt)
             18 -> do pos <- fromBin; e1 <- fromBin; e2 <- fromBin;
                      e3 <- fromBin; return (Cif pos e1 e2 e3)
             19 -> do pos <- fromBin; e1 <- fromBin; e2 <- fromBin;
                      return (CSub pos e1 e2)
             20 -> do e1 <- fromBin; e2 <- fromBin; e3 <- fromBin;
                      return (CSub2 e1 e2 e3)
             21 -> do pos <- fromBin; ss <- fromBin; return (Cmodule pos ss)
             22 -> do pos <- fromBin; mi <- fromBin; ds <- fromBin;
                      return (Cinterface pos mi ds)
             23 -> do e <- fromBin; b <- fromBin; vc <- fromBin;
                      vr <- fromBin; va <- fromBin; vf <- fromBin;
                      vs <- fromBin; vp <- fromBin;
                      return (CmoduleVerilog e b vc vr va vf vs vp)
             24 -> do i <- fromBin; qt <- fromBin; return (CForeignFuncC i qt)
             25 -> do b <- fromBin; ss <- fromBin; return (Cdo b ss)
             26 -> do pos <- fromBin; ss <- fromBin; return (Caction pos ss)
             27 -> do ps <- fromBin; rs <- fromBin; return (Crules ps rs)
             29 -> do ops <- fromBin; return (COper ops)
             30 -> do i1 <- fromBin; i2 <- fromBin; e <- fromBin;
                      return (CCon1 i1 i2 e)
             31 -> do i1 <- fromBin; e <- fromBin; i2 <- fromBin;
                      return (CSelectTT i1 e i2)
             32 -> do mi <- fromBin; i <- fromBin; return (CCon0 mi i)
             33 -> do i1 <- fromBin; i2 <- fromBin; es <- fromBin;
                      return (CConT i1 i2 es)
             34 -> do t <- fromBin; ies <- fromBin; return (CStructT t ies)
             35 -> do i1 <- fromBin; i2 <- fromBin; return (CSelectT i1 i2)
             36 -> do t <- fromBin; l <- fromBin; return (CLitT t l)
             37 -> do pos <- fromBin; uk <- fromBin; t <- fromBin;
                      return (CAnyT pos uk t)
             38 -> do t <- fromBin; e <- fromBin; b <- fromBin; vc <- fromBin;
                      vr <- fromBin; va <- fromBin; vf <- fromBin;
                      vs <- fromBin; vp <- fromBin;
                      return (CmoduleVerilogT t e b vc vr va vf vs vp)
             39 -> do i <- fromBin; t <- fromBin; return (CForeignFuncCT i t)
             40 -> do e <- fromBin; ts <- fromBin; return (CTApply e ts)
             41 -> do ps <- fromBin; return (Cattributes ps)
             42 -> do pos <- fromBin; e_vec <- fromBin; e_h <- fromBin;
                      e_l <- fromBin; e_rhs <- fromBin
                      return (CSubUpdate pos e_vec (e_h, e_l) e_rhs)
             n -> internalError $ "GenBin.Bin(CExpr).readBytes: " ++ show n

instance Bin CDefl where
    writeBytes (CLValueSign d qs) = do putI 0; toBin d; toBin qs
    writeBytes (CLValue i cs qs)  = do putI 1; toBin i; toBin cs; toBin qs
    writeBytes (CLMatch p e)  = do putI 2; toBin p; toBin e
    readBytes =
        do tag <- getI
           case tag of
            0 -> do d <- fromBin; qs <- fromBin; return (CLValueSign d qs)
            1 -> do i <- fromBin; cs <- fromBin; qs <- fromBin;
                    return (CLValue i cs qs)
            2 -> do p <- fromBin; e <- fromBin; return (CLMatch p e)
            n -> internalError $ "GenBin.Bin(CDefl).readBytes: " ++ show n

instance Bin CDef where
    writeBytes (CDef i qt cs) = do putI 0; toBin i; toBin qt; toBin cs
    writeBytes (CDefT i tvs qt cs) =
        do putI 1; toBin i; toBin tvs; toBin qt; toBin cs
    readBytes =
        do tag <- getI
           case tag of
            0 -> do i <- fromBin; qt <- fromBin; cs <- fromBin;
                    return (CDef i qt cs)
            1 -> do i <- fromBin; tvs <- fromBin; qt <- fromBin;
                    cs <- fromBin; return (CDefT i tvs qt cs)
            n -> internalError $ "GenBin.Bin(CDef).readBytes: " ++ show n

instance Bin CStmt where
    writeBytes (CSBindT p me ps qt e) =
        do putI 0; toBin p; toBin me; toBin ps; toBin qt; toBin e
    writeBytes (CSBind p me ps e) =
        do putI 1; toBin p; toBin me; toBin ps; toBin e
    writeBytes (CSletseq ds)  = do putI 2; toBin ds
    writeBytes (CSletrec ds)  = do putI 3; toBin ds
    writeBytes (CSExpr me e)  = do putI 4; toBin me; toBin e
    readBytes =
        do tag <- getI
           case tag of
            0 -> do p <- fromBin; me <- fromBin; ps <- fromBin; qt <- fromBin;
                    e <- fromBin; return (CSBindT p me ps qt e)
            1 -> do p <- fromBin; me <- fromBin; ps <- fromBin; e <- fromBin;
                    return (CSBind p me ps e)
            2 -> do ds <- fromBin; return (CSletseq ds)
            3 -> do ds <- fromBin; return (CSletseq ds)
            4 -> do me <- fromBin; e <- fromBin; return (CSExpr me e)
            n -> internalError $ "GenBin.Bin(CStmt).readBytes: " ++ show n

instance Bin CMStmt where
    writeBytes (CMStmt s) = do putI 0; toBin s
    writeBytes (CMrules e) = do putI 1; toBin e
    writeBytes (CMinterface e)  = do putI 2; toBin e
    writeBytes (CMTupleInterface pos es)  = do putI 3; toBin pos; toBin es
    readBytes =
        do tag <- getI
           case tag of
            0 -> do s <- fromBin; return (CMStmt s)
            1 -> do e <- fromBin; return (CMrules e)
            2 -> do e <- fromBin; return (CMinterface e)
            3 -> do pos <- fromBin; es <- fromBin;
                    return (CMTupleInterface pos es)
            n -> internalError $ "GenBin.Bin(CMStmt).readBytes: " ++ show n

instance Bin CCaseArm where
    writeBytes (CCaseArm p qs e) = do toBin p; toBin qs; toBin e
    readBytes = do p <- fromBin; qs <- fromBin; e <- fromBin;
                        return (CCaseArm p qs e)

instance Bin CRule where
    writeBytes (CRule ps me qs e) =
        do putI 0; toBin ps; toBin me; toBin qs; toBin e
    writeBytes (CRuleNest ps me qs rs) =
        do putI 1; toBin ps; toBin me; toBin qs; toBin rs
    readBytes =
        do tag <- getI
           case tag of
            0 -> do ps <- fromBin; me <- fromBin; qs <- fromBin; e <- fromBin;
                    return (CRule ps me qs e)
            1 -> do ps <- fromBin; me <- fromBin; qs <- fromBin; rs <- fromBin;
                    return (CRuleNest ps me qs rs)
            n -> internalError $ "GenBin.Bin(CRule).readBytes: " ++ show n


-- ----------
-- Bin Pragma

instance Bin Pragma where
    writeBytes (Pproperties i ps) = do putI 0; toBin i; toBin ps
    writeBytes (Pnoinline is)     = do putI 1; toBin is
    readBytes = do tag <- getI
                   case tag of
                     0 -> do i <- fromBin
                             ps <- fromBin
                             return (Pproperties i ps)
                     1 -> do is <- fromBin; return (Pnoinline is)
                     n -> internalError $ "GenBin.Bin(Pragma).readBytes: " ++ show n

-- ----------
-- Bin IPackage

instance Bin (IPackage a) where
    writeBytes pkg =
        section "IPackage" $
        do toBin (ipkg_name pkg)
           toBin (ipkg_depends pkg)
           toBin (ipkg_pragmas pkg)
           toBin (ipkg_defs pkg)
    readBytes = do when doTrace $ traceM("read IPackage")
                   name    <- fromBin
                   depends <- fromBin
                   pragmas <- fromBin
                   defs    <- fromBin
                   return $ IPackage { ipkg_name    = name
                                     , ipkg_depends = depends
                                     , ipkg_pragmas = pragmas
                                     , ipkg_defs    = defs
                                     }

-- ----------
-- Bin IDef

instance Bin (IDef a) where
    writeBytes (IDef i ty e p) =
        section "IDef" $
        do toBin i; toBin ty; toBin e ; toBin p
    readBytes = do when doTrace $ traceM("read IDef")
                   i <- fromBin
                   ty <- fromBin
                   e <- fromBin
                   p <- fromBin
                   return $ IDef i ty e p

-- ----------
-- Bin IExpr

instance Bin (IExpr a) where
    writeBytes (ILam i t e)   = do putI 0; toBin i; toBin t; toBin e
    writeBytes (IAps e ts es) = do putI 1; toBin e; toBin ts; toBin es
    writeBytes (IVar i)       = do putI 2; toBin i
    writeBytes (ILAM i k e)   = do putI 3; toBin i; toBin k; toBin e
    writeBytes (ICon i ic)    = do putI 4; toBin i; toBin ic
    writeBytes (IRefT _ _ _)  = internalError "GenBin.Bin(IExpr).writeBytes: IRefT"
    readBytes = do tag <- getI
                   case tag of
                     0 -> do i <- fromBin
                             t <- fromBin
                             e <- fromBin
                             return (ILam i t e)
                     1 -> do e <- fromBin
                             ts <- fromBin
                             es <- fromBin
                             return (IAps e ts es)
                     2 -> do i <- fromBin; return (IVar i)
                     3 -> do i <- fromBin
                             k <- fromBin
                             e <- fromBin
                             return (ILAM i k e)
                     4 -> do i <- fromBin; ic <- fromBin; return (ICon i ic)
                     n -> internalError $ "GenBin.Bin(IExpr).readBytes: " ++ show n

-- ----------
-- Bin ConTagInfo

instance Bin ConTagInfo where
  writeBytes (ConTagInfo conNo numCon conTag tagSize) =
    do toBin conNo; toBin numCon; toBin conTag; toBin tagSize
  readBytes = do
    conNo <- fromBin; numCon <- fromBin; conTag <- fromBin; tagSize <- fromBin
    return $ ConTagInfo conNo numCon conTag tagSize

-- ----------
-- Bin IConInfo

instance Bin (IConInfo a) where
    writeBytes (ICDef t _)      = do putI 0; toBin t
    writeBytes (ICPrim t p)     = do putI 1; toBin t; toBin (fromEnum p)
    writeBytes (ICForeign t n isC ps Nothing) =
        do putI 2; toBin t; toBin n; toBin isC; toBin ps
    writeBytes (ICForeign { fcallNo = (Just _) }) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICForeign with cookie"
    writeBytes (ICCon t cti)    = do putI 3; toBin t; toBin cti
    writeBytes (ICIs t cti)     = do putI 4; toBin t; toBin cti
    writeBytes (ICOut t cti)    = do putI 5; toBin t; toBin cti
    writeBytes (ICTuple t is)   = do putI 6; toBin t; toBin is
    writeBytes (ICSel t i j)    = do putI 7; toBin t; toBin i; toBin j
    writeBytes (ICVerilog t ui v tss) =
        do putI 8; toBin t; toBin ui; toBin v; toBin tss
    writeBytes (ICUndet t u mv) = do putI 9; toBin t; toBin u; toBin mv
    writeBytes (ICInt t v)      = do putI 10; toBin t; toBin v
    writeBytes (ICReal t v)     = do putI 11; toBin t; toBin v
    writeBytes (ICString t s)   = do putI 12; toBin t; toBin s
    writeBytes (ICChar t c)     = do putI 13; toBin t; toBin c
    writeBytes (ICRuleAssert t as) = do putI 14; toBin t; toBin as
    writeBytes (ICSchedPragmas t sps) = do putI 15; toBin t; toBin sps
    writeBytes (ICName t n)     = do putI 16; toBin t; toBin n
    writeBytes (ICAttrib t pps) = do putI 17; toBin t; toBin pps;
    writeBytes (ICPosition t pos) = do putI 18; toBin t; toBin pos
    writeBytes (ICType t it)    = do putI 19; toBin t; toBin it
    writeBytes (ICIFace _ _ _) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICIFace"
    writeBytes (ICValue _ _) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICValue"
    writeBytes (ICMethArg _) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICMethArg"
    writeBytes (ICModPort _) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICModPort"
    writeBytes (ICModParam _) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICModParam"
    writeBytes (ICStateVar _ _) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICStateVar"
    writeBytes (ICClock _ _) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICClock"
    writeBytes (ICReset _ _) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICReset"
    writeBytes (ICInout _ _) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICInout"
    writeBytes (ICLazyArray _ _ _) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICLazyArray"
    writeBytes (ICPred _ _) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICPred"
    writeBytes (ICHandle { }) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICHandle"
    writeBytes (ICMethod { }) =
        internalError "GenBin.Bin(IConInfo).writeBytes: ICMethod"
    readBytes = do tag <- getI
                   t <- fromBin
                   case tag of
                     0  -> -- ICDef contains the expression for the def
                           -- Here we use a don't-care value for the expression
                           -- XXX Should we use an error there, so it's not silently used?
                           return (ICDef t (icUndet t UNoMatch))
                     1  -> do p <- fromBin; return (ICPrim t (toEnum p))
                     2  -> do n <- fromBin
                              isC <- fromBin
                              ps <- fromBin
                              return (ICForeign t n isC ps Nothing)
                     3  -> do cti <- fromBin; return (ICCon t cti)
                     4  -> do cti <- fromBin; return (ICIs t cti)
                     5  -> do cti <- fromBin; return (ICOut t cti)
                     6  -> do is <- fromBin; return (ICTuple t is)
                     7  -> do i <- fromBin; j <- fromBin; return (ICSel t i j)
                     8  -> do ui <- fromBin
                              v <- fromBin
                              tss <- fromBin
                              return (ICVerilog t ui v tss)
                     9  -> do u <- fromBin
                              mv <- fromBin
                              return (ICUndet t u mv)
                     10 -> do v <- fromBin; return (ICInt t v)
                     11 -> do v <- fromBin; return (ICReal t v)
                     12 -> do s <- fromBin; return (ICString t s)
                     13 -> do c <- fromBin; return (ICChar t c)
                     14 -> do as <- fromBin; return (ICRuleAssert t as)
                     15 -> do sps <- fromBin; return (ICSchedPragmas t sps)
                     16 -> do n <- fromBin; return (ICName t n)
                     17 -> do pps <- fromBin; return (ICAttrib t pps)
                     18 -> do pos <- fromBin; return (ICPosition t pos)
                     19 -> do it <- fromBin; return (ICType t it)
                     n  -> internalError $ "GenBin.Bin(IConInfo).readBytes: " ++ show n
