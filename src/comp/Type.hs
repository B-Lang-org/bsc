module Type where
import ErrorUtil(internalError)
import Id(Id)
import Position(Position, noPosition)
import PreIds
import PPrint(ppReadable)
import CType(Type(..), TyVar(..), TyCon(..), TISort(..), Kind(..), StructSubType(..), cTNum)

infixr 4 `fn`

-- XXX these definitions should be synced with StdPrel.hs where applicable

tArrow, tBit, tInt :: Type
tArrow = TCon (TyCon (idArrow noPosition) (Just (Kfun KStar (Kfun KStar KStar))) TIabstract)
tBit = TCon (TyCon idBit (Just (Kfun KNum KStar)) TIabstract)
tInt = TCon (TyCon idInt (Just (Kfun KNum KStar)) TIabstract)

tIntAt :: Position -> Type
tIntAt pos = TCon (TyCon (idIntAt pos) (Just (Kfun KNum KStar)) TIabstract)

tiData, tiEnum :: [Id] -> TISort
tiEnum cons = TIdata { tidata_cons = cons, tidata_enum = True }
tiData cons = TIdata { tidata_cons = cons, tidata_enum = False }

tUInt, tBool, tPrimUnit :: Type
tUInt = TCon (TyCon idUInt (Just (Kfun KNum KStar)) TIabstract)
tBool = TCon (TyCon idBool (Just KStar) (tiEnum [idFalse, idTrue]))
--tArray = TCon (TyCon idArray (Just (Kfun KNum (Kfun KNum KStar))) (TIstruct SInterface [id_sub, id_upd]))
tPrimUnit = TCon (TyCon idPrimUnit (Just KStar) (TIstruct SStruct []))

tPrimUnitAt :: Position -> Type
tPrimUnitAt pos = TCon (TyCon (idPrimUnitAt pos) (Just KStar) (TIstruct SStruct []))

tInteger, tReal :: Type
tInteger = TCon (TyCon idInteger (Just KStar) TIabstract)
tReal = TCon (TyCon idReal (Just KStar) TIabstract)

tRealAt :: Position -> Type
tRealAt pos = TCon (TyCon (idRealAt pos) (Just KStar) TIabstract)

tClock, tReset, tInout, tInout_, tChar, tString :: Type
tClock = TCon (TyCon idClock (Just KStar) TIabstract)
tReset = TCon (TyCon idReset (Just KStar) TIabstract)
tInout = TCon (TyCon idInout (Just (Kfun KStar KStar)) TIabstract)
tInout_ = TCon (TyCon idInout_ (Just (Kfun KNum KStar)) TIabstract)
tString = TCon (TyCon idString (Just KStar) TIabstract)
tChar = TCon (TyCon idChar (Just KStar) TIabstract)

tFmt, tName, tPosition, tType :: Type
tFmt = TCon (TyCon idFmt (Just KStar) TIabstract)
tName = TCon (TyCon idName (Just KStar) TIabstract)
tPosition = TCon (TyCon idPosition (Just KStar) TIabstract)
tType = TCon (TyCon idType (Just KStar) TIabstract)

tPred, tAttributes, tPrimPair, tSizeOf :: Type
tPred = TCon (TyCon idPred (Just KStar) TIabstract)
tAttributes = TCon (TyCon idAttributes (Just KStar) TIabstract)
tPrimPair = TCon (TyCon idPrimPair (Just (Kfun KStar (Kfun KStar KStar))) (TIstruct SStruct [idPrimFst, idPrimSnd]))
tSizeOf = TCon (TyCon idSizeOf (Just (Kfun KStar KNum)) TIabstract)

tAction, tActionValue, tActionValue_, tAction_:: Type
tAction = TCon (TyCon idAction (Just KStar) (TItype 0 (TAp tActionValue tPrimUnit)))
tActionValue = TCon (TyCon idActionValue (Just (Kfun KStar KStar)) (TIstruct SStruct [id__value, id__action]))
tActionValue_ = TCon (TyCon idActionValue_ (Just (Kfun KStar KStar)) (TIstruct SStruct [id__value, id__action]))
tAction_ = TAp tActionValue_ tPrimUnit

tActionAt, tActionValueAt, tActionValue_At :: Position -> Type
tActionAt pos = TCon (TyCon (idActionAt pos) (Just KStar) (TItype 0 (TAp (tActionValueAt pos) (tPrimUnitAt pos))))
tActionValueAt pos = TCon (TyCon (idActionValueAt pos) (Just (Kfun KStar KStar)) (TIstruct SStruct [id__value_at pos, id__action_at pos]))
tActionValue_At pos = TCon (TyCon (idActionValue_At pos) (Just (Kfun KStar KStar)) (TIstruct SStruct [id__value_at pos, id__action_at pos]))

tPrimAction, tRules :: Type
tPrimAction = TCon (TyCon idPrimAction (Just KStar) TIabstract)
tRules = TCon (TyCon idRules (Just KStar) TIabstract)

tRulesAt :: Position -> Type
tRulesAt pos = TCon (TyCon (idRulesAt pos) (Just KStar) TIabstract)

tSchedPragma, tModule, tVRWireN, tId, t32 :: Type
tSchedPragma = TCon (TyCon idSchedPragma (Just KStar) TIabstract)
tModule = TCon (TyCon idModule (Just (Kfun KStar KStar)) TIabstract)
tVRWireN = TCon (TyCon idVRWireN (Just (Kfun KNum KStar)) (TIstruct SStruct [idWSet, idWGet, idWHas]))
tId = TCon (TyCon idId (Just (Kfun KStar KStar)) TIabstract)
t32 = tOfSize 32 noPosition

t32At :: Position -> Type
t32At pos = tOfSize 32 pos

tOfSize :: Integer -> Position -> Type
tOfSize n pos = cTNum n pos

tInt32At :: Position -> Type
tInt32At pos = TAp (tIntAt pos) (t32At pos)

tBitN :: Integer -> Position -> Type
tBitN n pos = TAp tBit (tOfSize n pos)

tNat :: Position -> Type
tNat pos = tBitN 32 pos

tFile, tSvaParam :: Type
tFile = TCon (TyCon idFile (Just KStar) TIabstract)
tSvaParam  = TCon (TyCon idSvaParam (Just KStar) (tiData [idSvaBool, idSvaNumber]))

fn         :: Type -> Type -> Type
a `fn` b    = TAp (TAp tArrow a) b

-- numeric kinds and type constructors
kNNN, kNN, kNNS, kNS :: Kind
kNNN = Kfun KNum kNN
kNN = Kfun KNum KNum

kNNS = Kfun KNum kNS
kNS  = Kfun KNum KStar

tAdd, tSub, tMul, tDiv, tLog, tExp, tMax, tMin :: Type
tAdd = TCon (TyCon idTAdd (Just kNNN) TIabstract)
tSub = TCon (TyCon idTSub (Just kNNN) TIabstract)
tMul = TCon (TyCon idTMul (Just kNNN) TIabstract)
tDiv = TCon (TyCon idTDiv (Just kNNN) TIabstract)
tLog = TCon (TyCon idTLog (Just kNN)  TIabstract)
tExp = TCon (TyCon idTExp (Just kNN)  TIabstract)
tMax = TCon (TyCon idTMax (Just kNNN) TIabstract)
tMin = TCon (TyCon idTMin (Just kNNN) TIabstract)

class HasKind t where
    kind :: t -> Kind

instance HasKind TyVar where
    kind (TyVar v _ k) = k

instance HasKind TyCon where
    kind (TyCon v (Just k) _) = k
    kind (TyNum _ _) = KNum
    kind (TyStr _ _) = KStr
    kind (TyCon v Nothing _) = internalError "Type.HasKind(TyCon).kind: TyCon without kind"

instance HasKind Type where
    kind (TCon tc) = kind tc
    kind (TVar u)  = kind u
    kind tt@(TAp t _) = case kind t of
                        Kfun _ k -> k
                        k        ->
                         internalError ("kind: " ++ ppReadable k ++ (show tt) ++ "\n")
    kind (TGen _ _)  = internalError "Type.HasKind(Type).kind: TGen"
    kind (TDefMonad _) = internalError "Type.HasKind(Type).kind: TDefMonad"

arrow :: Type -> Type -> Type
arrow a r = TAp (TAp tArrow a) r


-- -------------------------

-- XXX kill this
isPrimAction :: Type -> Bool
isPrimAction t = t == tPrimAction

isActionValue :: Type -> Bool
isActionValue (TAp av _) = av == tActionValue
isActionValue _ = False

getAVType :: Type -> Type
getAVType (TAp av t) | av == tActionValue = t
getAVType t = internalError("getAVType not ActionValue: " ++ ppReadable t)

-- Note that we consider ActionValue_ (Bit 0) to be an action without a value,
-- as this is still created by foreign verilog module imports.
-- XXX should rework this to just yield ActionValue_ () for empty types.
isActionWithoutValue :: Type -> Bool
isActionWithoutValue (TAp av (TAp (TCon (TyCon i _ _)) (TCon (TyNum 0 _)))) =
    av == tActionValue_ && i == idBit
isActionWithoutValue (TAp av (TCon (TyCon i _ _))) =
    av == tActionValue_ && i == idPrimUnit
isActionWithoutValue _ = False

isActionWithValue :: Type -> Bool
isActionWithValue (TAp av (TVar _)) = av == tActionValue_
isActionWithValue (TAp av (TAp (TCon (TyCon i _ _)) (TCon (TyNum 0 _))))
    | av == tActionValue_ && i == idBit = False
isActionWithValue (TAp av t) = (av == tActionValue_) && isBitTuple t
isActionWithValue _ = False

isClock, isReset, isInout, isInout_ :: Type -> Bool
isClock t = t == tClock
isReset t = t == tReset

isInout (TAp i _) = i == tInout
isInout _ = False

isInout_ (TAp i _) = i == tInout_
isInout_ _ = False

isBit, isInt, isUInt, isBool, isInteger, isString, isChar, isReal, isFmt :: Type -> Bool
isBit (TAp b _) = b == tBit
isBit _ = False

isInt (TAp i _) = i == tInt
isInt _ = False

isUInt (TAp u _) = u == tUInt
isUInt _ = False

isBool t = t == tBool
isInteger t = t == tInteger
isString t = t == tString
isChar t = t == tChar
isReal t = t == tReal
isFmt t = t == tFmt

isBitTuple :: Type -> Bool
isBitTuple (TAp (TAp (TCon (TyCon i _ _)) t1) t2) | i == idPrimPair =
    isBit t1 && isBitTuple t2
isBitTuple t = isBit t

-- -------------------------
