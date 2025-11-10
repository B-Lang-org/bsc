module INormTypes(iNormTypes) where

import qualified Data.Map as M

import ErrorUtil(internalError)
import Util(mapSnd)
import PPrint(ppReadable)
import Flags(Flags)

import PreIds(idSizeOf)
import ISyntax
import IConv(iConvT)
import SymTab

iNormTypes :: Flags -> SymTab -> IModule a -> IModule a
iNormTypes flags symt = iNorm fullNorm
  where fullNorm c@(ITCon _ _ _)    = c
        fullNorm n@(ITNum _)        = n
        fullNorm s@(ITStr _)        = s
        fullNorm v@(ITVar i)        = v
        fullNorm (ITForAll i k t)   = ITForAll i k $ fullNorm t
        fullNorm (ITAp f@(ITCon op _ _) a)
          | op == idSizeOf && canNorm a' = normalizeSizeOf $ ITAp f a'
          where a' = fullNorm a
                -- iToCT which we use below cannot handle ITVar and ITForAll
                canNorm (ITVar _)        = False
                canNorm (ITForAll _ _ _) = False
                canNorm (ITAp f a)       = canNorm f && canNorm a
                canNorm _                = True
        fullNorm t@(ITAp f a) = normITAp f' a'
          where f' = fullNorm f
                a' = fullNorm a
        normalizeSizeOf t =
          let t' = iConvT flags symt $ iToCT t
          in case t' of
               ITNum _ -> t'
               _ -> internalError $ "iNormTypes - unsimplified: " ++ ppReadable (t,t')

class INormTypes a where
  iNorm :: (IType -> IType) -> a -> a

instance INormTypes a => INormTypes [a] where
  iNorm f = map (iNorm f)

instance INormTypes (IModule a) where
  iNorm f imod = imod {
    imod_wire_args = iNorm f (imod_wire_args imod),
    imod_clock_domains = mapSnd (iNorm f) (imod_clock_domains imod),
    imod_resets = iNorm f (imod_resets imod),
    imod_state_insts = mapSnd (iNorm f) (imod_state_insts imod),
    imod_port_types = M.map (M.map f) (imod_port_types imod),
    imod_local_defs = iNorm f (imod_local_defs imod),
    imod_rules = iNorm f (imod_rules imod),
    imod_interface = iNorm f (imod_interface imod)
  }

instance INormTypes (IDef a) where
  iNorm f (IDef i t e props) = IDef i (f t) (iNorm f e) props

instance INormTypes (IExpr a) where
  iNorm f (IAps e ts es) = IAps (iNorm f e) (map f ts) (iNorm f es)
  iNorm f (ICon i ic) = ICon i (iNorm f ic)
  iNorm f e = internalError $ "iNormTypes - unexpected IExpr: " ++ ppReadable e

instance INormTypes (IConInfo a) where
  iNorm f (ICPrim t op) = ICPrim (f t) op
  iNorm f (ICForeign t name isC ports callNo) = ICForeign (f t) name isC ports callNo
  iNorm f (ICSel t sel num) = ICSel (f t) sel num
  iNorm f (ICStateVar t isv) = ICStateVar (f t) (iNorm f isv)
  iNorm f (ICUndet t kind mval) = ICUndet (f t) kind (fmap (iNorm f) mval)
  iNorm f (ICInt t v) = ICInt (f t) v
  iNorm f (ICReal t r) = ICReal (f t) r
  iNorm f (ICString t s) = ICString (f t) s
  iNorm f (ICMethArg t) = ICMethArg (f t)
  iNorm f (ICModPort t) = ICModPort (f t)
  iNorm f (ICModParam t) = ICModParam (f t)
  iNorm f (ICValue t e) = ICValue (f t) (iNorm f e)
  iNorm f (ICClock t c) = ICClock (f t) (iNorm f c)
  iNorm f (ICReset t r) = ICReset (f t) (iNorm f r)
  iNorm f (ICInout t io) = ICInout (f t) (iNorm f io)
  iNorm f (ICTuple t fs) = ICTuple (f t) fs
  iNorm f ic = internalError $ "iNormTypes - unexpected IConInfo: " ++ show ic

instance INormTypes (IEFace a) where
  iNorm f iface = iface {
    ief_args = mapSnd f (ief_args iface),
    ief_value = fmap (\(e, t) -> (iNorm f e, f t)) (ief_value iface),
    ief_body = fmap (iNorm f) (ief_body iface)
  }

instance INormTypes (IStateVar a) where
  iNorm f isv = isv {
    isv_iargs = iNorm f (isv_iargs isv),
    isv_type = f (isv_type isv),
    isv_meth_types = map (map f) (isv_meth_types isv),
    isv_clocks = mapSnd (iNorm f) (isv_clocks isv),
    isv_resets = mapSnd (iNorm f) (isv_resets isv)
  }

instance INormTypes IAbstractInput where
  iNorm f (IAI_Port (i, t)) = IAI_Port (i, f t)
  iNorm f iai = iai

instance INormTypes (IClock a) where
  iNorm f ic = setClockWires ic (iNorm f $ getClockWires ic)

instance INormTypes (IReset a) where
  iNorm f ir = makeReset (getResetId ir)
                         (iNorm f $ getResetClock ir)
                         (iNorm f $ getResetWire ir)

instance INormTypes (IInout a) where
  iNorm f io = makeInout (iNorm f $ getInoutClock io)
                         (iNorm f $ getInoutReset io)
                         (iNorm f $ getInoutWire io)

instance INormTypes (IRules a) where
  iNorm f (IRules sps rules) = IRules sps (iNorm f rules)

instance INormTypes (IRule a) where
  iNorm f rule = rule {
    irule_pred = iNorm f (irule_pred rule),
    irule_body = iNorm f (irule_body rule)
  }
