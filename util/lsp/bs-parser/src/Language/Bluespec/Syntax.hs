{-# LANGUAGE DeriveGeneric #-}

-- | Abstract syntax tree definitions for Bluespec Classic.
module Language.Bluespec.Syntax
  ( -- * Package
    Package (..)
  , Export (..)
  , Import (..)
  , ImportSpec (..)

    -- * Identifiers
  , Ident (..)
  , ModuleId (..)
  , QualIdent (..)
  , mkIdent
  , mkQualIdent
  , identText

    -- * Definitions
  , Definition (..)
  , Clause (..)
  , Guard
  , GuardQual (..)
  , LetItem (..)
  , Binding (..)
  , Field (..)
  , Constructor (..)
  , Deriving (..)
  , ClassMember (..)
  , InstanceMember (..)
  , FunDep (..)
  , TopLevelPragma (..)

    -- * Types
  , Type (..)
  , QualType (..)
  , Pred (..)
  , TyVar (..)
  , Kind (..)

    -- * Expressions
  , Expr (..)
  , Alt (..)
  , Stmt (..)
  , FieldBind (..)

    -- * Patterns
  , Pattern (..)

    -- * Literals
  , Literal (..)
  , IntFormat (..)

    -- * Operators
  , Op (..)
  , Fixity (..)
  , FixityDir (..)
  , FixityDecl (..)

    -- * Module/Interface/Rules
  , ModuleStmt (..)
  , InterfaceField (..)
  , Rule (..)
  , RulePragma (..)
  , MethodPragma (..)

    -- * Verilog module
  , VerilogMethod (..)
  , PortSpec (..)
  , PortProp (..)
  , SchedInfo (..)
  , SchedEntry (..)
  , SchedOp

    -- * Located type aliases
  , LIdent
  , LExpr
  , LType
  , LPattern
  , LDefinition
  , LStmt
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)

import Language.Bluespec.Position

--------------------------------------------------------------------------------
-- Identifiers
--------------------------------------------------------------------------------

-- | An identifier (variable or constructor name).
data Ident
  = VarId !Text   -- ^ lowercase identifier (variable, type variable)
  | ConId !Text   -- ^ uppercase identifier (constructor, type constructor)
  deriving stock (Eq, Ord, Show, Generic)

-- | Create an identifier from text.
mkIdent :: Text -> Ident
mkIdent t = case T.uncons t of
  Just (c, _) | c >= 'A' && c <= 'Z' -> ConId t
  _ -> VarId t

-- | Get the text of an identifier.
identText :: Ident -> Text
identText (VarId t) = t
identText (ConId t) = t

-- | A module identifier.
newtype ModuleId = ModuleId { unModuleId :: Text }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Semigroup, Monoid)

-- | A possibly qualified identifier.
data QualIdent = QualIdent
  { qualModule :: !(Maybe ModuleId)
  , qualIdent  :: !Ident
  }
  deriving stock (Eq, Ord, Show, Generic)

-- | Create a qualified identifier.
mkQualIdent :: Maybe ModuleId -> Ident -> QualIdent
mkQualIdent = QualIdent

--------------------------------------------------------------------------------
-- Package
--------------------------------------------------------------------------------

-- | A Bluespec package (compilation unit).
data Package = Package
  { pkgSpan    :: !SrcSpan
  , pkgName    :: !(Located ModuleId)
  , pkgExports :: !(Maybe [Located Export])
  , pkgImports :: ![Located Import]
  , pkgFixity  :: ![Located FixityDecl]
  , pkgDefns   :: ![LDefinition]
  }
  deriving stock (Eq, Show, Generic)

-- | An export specification.
data Export
  = ExportVar !Ident                     -- ^ Export a variable
  | ExportType !Ident !(Maybe [Ident])   -- ^ Export a type with optional constructors
  | ExportModule !ModuleId               -- ^ Re-export a module
  deriving stock (Eq, Show, Generic)

-- | An import declaration.
data Import = Import
  { importQualified :: !Bool
  , importModule    :: !ModuleId
  , importAs        :: !(Maybe ModuleId)
  , importSpec      :: !(Maybe ImportSpec)
  }
  deriving stock (Eq, Show, Generic)

-- | Import specification (hiding or explicit).
data ImportSpec
  = ImportOnly ![Located Export]   -- ^ Import only these
  | ImportHiding ![Located Export] -- ^ Import all except these
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Definitions
--------------------------------------------------------------------------------

type LDefinition = Located Definition

-- | A top-level definition.
data Definition
  = DefValue !(Located Ident) !(Maybe (Located QualType)) ![Clause]
    -- ^ Value/function definition
  | DefTypeSig !(Located Ident) !(Located QualType)
    -- ^ Type signature (separate from value definition)
  | DefType !(Located Ident) !(Maybe (Located Kind)) ![Located TyVar] !(LType)
    -- ^ Type synonym (with optional kind annotation on the type name)
  | DefData !(Located Ident) !(Maybe (Located Kind)) ![Located TyVar] ![Located Constructor] ![Deriving]
    -- ^ Data type definition (with optional kind annotation on the type name)
  | DefInterface !(Located Ident) ![Located TyVar] ![Located Field] ![Deriving]
    -- ^ Interface (struct-like) definition
  | DefClass !(Maybe Bool) ![Located Pred] !(Located Ident) ![Located TyVar] ![FunDep] ![ClassMember]
    -- ^ Type class definition. Maybe Bool: Nothing = regular, Just False = coherent, Just True = incoherent
  | DefInstance ![Located Pred] !(Located QualIdent) ![LType] ![InstanceMember]
    -- ^ Type class instance
  | DefPrimitive !(Located Ident) !(Located QualType)
    -- ^ Primitive value declaration
  | DefPrimitiveType !(Located Ident) !(Located Kind)
    -- ^ Primitive type declaration (e.g., primitive type Id__ :: * -> *)
  | DefForeign !(Located Ident) !(Located QualType) !(Maybe Text)
    -- ^ Foreign import
  | DefPragma !TopLevelPragma
    -- ^ Top-level pragma (e.g., {-# properties ... #-})
  deriving stock (Eq, Show, Generic)

-- | A function clause (one equation).
data Clause = Clause
  { clauseSpan  :: !SrcSpan
  , clausePats  :: ![LPattern]
  , clauseGuard :: !(Maybe Guard)
  , clauseBody  :: !LExpr
  , clauseWhere :: ![LDefinition]
  }
  deriving stock (Eq, Show, Generic)

-- | A guard is a list of qualifiers, each either a boolean expression
-- or a pattern guard (pat <- exp).
-- In Bluespec: when qual1, qual2, ...
type Guard = [GuardQual]

-- | A single guard qualifier.
data GuardQual
  = BoolGuard !LExpr           -- ^ Simple boolean guard
  | PatGuard !LPattern !LExpr  -- ^ Pattern guard: pat <- exp
  deriving stock (Eq, Show, Generic)

-- | An item in a let/letseq/where block.
-- This can be either a standalone type signature or a binding.
data LetItem
  = LetTypeSig !(Located Ident) !(Located QualType)  -- ^ Type signature: x :: T
  | LetBind !Binding                                  -- ^ Value binding: x = e
  deriving stock (Eq, Show, Generic)

-- | A let/where binding.
-- For function-style bindings like @f x y = expr@, bindPat is the function name
-- and bindArgs contains the argument patterns. For simple pattern bindings like
-- @(a, b) = expr@, bindArgs is empty.
data Binding = Binding
  { bindSpan :: !SrcSpan
  , bindPat  :: !LPattern
  , bindArgs :: ![LPattern]  -- ^ Function arguments (empty for pattern bindings)
  , bindType :: !(Maybe (Located QualType))
  , bindExpr :: !LExpr
  }
  deriving stock (Eq, Show, Generic)

-- | A field in an interface/struct definition.
data Field = Field
  { fieldSpan    :: !SrcSpan
  , fieldName    :: !(Located Ident)
  , fieldType    :: !(Located QualType)  -- ^ Field type, possibly with class constraints
  , fieldPragmas :: ![MethodPragma]
  , fieldDefault :: !(Maybe LExpr)
  }
  deriving stock (Eq, Show, Generic)

-- | A data constructor.
-- conNames supports the Bluespec alias syntax: (Name1, Name2) for multiple names.
data Constructor = Constructor
  { conNames  :: ![Located Ident]  -- ^ Constructor names (aliases)
  , conFields :: ![LType]          -- ^ Positional fields
  , conRecord :: !(Maybe [Located Field])  -- ^ Record fields (if any)
  }
  deriving stock (Eq, Show, Generic)

-- | A deriving clause.
data Deriving = Deriving
  { derivingClass :: !(Located QualIdent)
  }
  deriving stock (Eq, Show, Generic)

-- | A class member declaration.
data ClassMember
  = ClassMethod !(Located Ident) !(Located QualType) !(Maybe LExpr)
    -- ^ Type signature with optional inline default: varId :: Type [= expr]
  | ClassDefaultImpl !(Located Ident) ![LPattern] !LExpr
    -- ^ Default implementation clause: varId [pats] = expr
  | ClassFixity !(Located FixityDecl)
  deriving stock (Eq, Show, Generic)

-- | An instance member definition.
data InstanceMember
  = InstanceMethod !(Located Ident) ![Clause]
  | InstanceTypeSig !(Located Ident) !(Located QualType)  -- ^ Type signature for method
  deriving stock (Eq, Show, Generic)

-- | A functional dependency.
data FunDep = FunDep
  { fdFrom :: ![Located TyVar]
  , fdTo   :: ![Located TyVar]
  }
  deriving stock (Eq, Show, Generic)

-- | A top-level pragma (e.g., {-# properties foo = { bar } #-}).
data TopLevelPragma = TopLevelPragma
  { tlpKind    :: !Text                       -- ^ Pragma kind (e.g., "properties", "synthesize")
  , tlpName    :: !(Maybe (Located Ident))    -- ^ Optional name being annotated
  , tlpContent :: !Text                       -- ^ Raw content after the name (unparsed)
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

type LType = Located Type

-- | A type expression.
data Type
  = TVar !(Located TyVar)              -- ^ Type variable
  | TCon !(Located QualIdent)          -- ^ Type constructor
  | TApp !LType !LType                 -- ^ Type application
  | TArrow !LType !LType               -- ^ Function type
  | TTuple ![LType]                    -- ^ Tuple type
  | TList !LType                       -- ^ List type
  | TNum !Integer                      -- ^ Numeric type literal
  | TString !Text                      -- ^ String type literal
  | TKind !LType !(Located Kind)       -- ^ Kind annotation
  deriving stock (Eq, Show, Generic)

-- | A qualified type (with constraints).
data QualType = QualType
  { qtPreds :: ![Located Pred]
  , qtType  :: !LType
  }
  deriving stock (Eq, Show, Generic)

-- | A type class predicate (constraint).
data Pred = Pred
  { predClass :: !(Located QualIdent)
  , predArgs  :: ![LType]
  }
  deriving stock (Eq, Show, Generic)

-- | A type variable.
data TyVar = TyVar
  { tvName :: !Ident
  , tvKind :: !(Maybe Kind)
  }
  deriving stock (Eq, Ord, Show, Generic)

-- | A kind expression.
data Kind
  = KStar                    -- ^ Type kind (*)
  | KNum                     -- ^ Numeric kind (#)
  | KString                  -- ^ String kind ($)
  | KArrow !Kind !Kind       -- ^ Function kind
  deriving stock (Eq, Ord, Show, Generic)

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

type LExpr = Located Expr

-- | An expression.
data Expr
  = EVar !(Located QualIdent)                    -- ^ Variable
  | ECon !(Located QualIdent)                    -- ^ Constructor
  | ELit !(Located Literal)                      -- ^ Literal
  | EApp !LExpr !LExpr                           -- ^ Application
  | EInfix !LExpr !(Located Op) !LExpr           -- ^ Infix operator application
  | ENeg !LExpr                                  -- ^ Unary negation
  | ELam ![LPattern] !LExpr                      -- ^ Lambda abstraction
  | ELet ![LetItem] !LExpr                       -- ^ Let expression (parallel)
  | ELetSeq ![LetItem] !LExpr                    -- ^ Letseq expression (sequential)
  | EWhere !LExpr ![Definition]                  -- ^ Expression with where clause: expr where { defns }
  | EIf !LExpr !LExpr !LExpr                     -- ^ If-then-else
  | ECase !LExpr ![Alt]                          -- ^ Case expression
  | EDo ![LStmt]                                 -- ^ Do notation
  | ETuple ![LExpr]                              -- ^ Tuple
  | EList ![LExpr]                               -- ^ List literal
  | ERecord !(Located QualIdent) ![FieldBind]    -- ^ Record construction
  | ERecordUpd !LExpr ![FieldBind]               -- ^ Record update
  | EFieldAccess !LExpr !(Located Ident)         -- ^ Field access (e.g., x.field)
  | EFieldSection !(Located Ident)               -- ^ Field section (e.g., (.field) = \x -> x.field)
  | EBitSelect !LExpr !LExpr !LExpr              -- ^ Bit selection (e.g., x[hi:lo])
  | ETypeSig !LExpr !(Located QualType)          -- ^ Type signature
  | EModule ![ModuleStmt]                        -- ^ Module expression
  | ERules ![Located Rule]                       -- ^ Rules expression
  | EInterface !(Maybe (Located QualIdent)) ![InterfaceField]  -- ^ Interface expression
  | EValueOf !LType                              -- ^ valueOf type
  | EStringOf !LType                             -- ^ stringOf type
  | EPrim !Text ![LExpr]                         -- ^ Primitive operation ($display, etc.)
  | EParens !LExpr                               -- ^ Parenthesized expression
  | EModuleVerilog                               -- ^ Verilog module import
      { vModName     :: !LExpr                   -- ^ Module name expression (string)
      , vModParams   :: ![LExpr]                 -- ^ Parameters (compile-time constants)
      , vModClocks   :: ![Text]                  -- ^ Clock port names
      , vModResets   :: ![Text]                  -- ^ Reset port names
      , vModArgs     :: ![(Text, LExpr)]         -- ^ Additional arguments (port name, value)
      , vModMethods  :: ![VerilogMethod]         -- ^ Method definitions
      , vModSched    :: !(Maybe SchedInfo)       -- ^ Scheduling information
      }
  -- BSV-specific expressions
  | ETagged !(Located Ident) ![(Located Ident, LExpr)]  -- ^ tagged Foo { field: val, ... }
  | EDontCare                                            -- ^ ? (don't-care wildcard)
  | EBeginEnd ![LStmt] !(Maybe LExpr)                   -- ^ begin { stmts } [expr] end
  deriving stock (Eq, Show, Generic)

-- | A case alternative.
data Alt = Alt
  { altSpan  :: !SrcSpan
  , altPat   :: !LPattern
  , altGuard :: !(Maybe Guard)
  , altBody  :: !LExpr
  }
  deriving stock (Eq, Show, Generic)

type LStmt = Located Stmt

-- | A statement in do-notation or a module.
data Stmt
  = StmtBind !LPattern !(Maybe (Located QualType)) !LExpr  -- ^ Pattern binding
  | StmtLet ![LetItem]                                     -- ^ Let bindings
  | StmtLetSeq ![LetItem]                                  -- ^ Sequential let bindings
  | StmtAssign !LExpr !LExpr                               -- ^ Register assignment (lhs := rhs or lhs <= rhs in BSV)
  | StmtExpr !LExpr                                        -- ^ Expression statement
  -- BSV-specific statements
  | StmtFor !LStmt !LExpr !LStmt ![LStmt]                  -- ^ for (init; cond; incr) { body }
  | StmtWhile !LExpr ![LStmt]                              -- ^ while (cond) body
  | StmtRepeat !LExpr ![LStmt]                             -- ^ repeat (n) body
  | StmtContinue                                           -- ^ continue
  | StmtBreak                                              -- ^ break
  | StmtReturn !LExpr                                      -- ^ return expr
  deriving stock (Eq, Show, Generic)

-- | A field binding in a record expression.
data FieldBind = FieldBind
  { fbSpan  :: !SrcSpan
  , fbName  :: !(Located Ident)
  , fbValue :: !LExpr
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

type LPattern = Located Pattern

-- | A pattern.
data Pattern
  = PVar !(Located Ident)                        -- ^ Variable pattern
  | PCon !(Located QualIdent) ![LPattern]        -- ^ Constructor pattern
  | PInfix !LPattern !(Located Op) !LPattern     -- ^ Infix constructor pattern
  | PLit !(Located Literal)                      -- ^ Literal pattern
  | PWild                                        -- ^ Wildcard (_)
  | PTuple ![LPattern]                           -- ^ Tuple pattern
  | PList ![LPattern]                            -- ^ List pattern
  | PRecord !(Located QualIdent) ![(Located Ident, LPattern)]  -- ^ Record pattern
  | PAs !(Located Ident) !LPattern               -- ^ As-pattern (x@p)
  | PTypeSig !LPattern !(Located QualType)       -- ^ Pattern with type sig
  | PParens !LPattern                            -- ^ Parenthesized pattern
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Literals
--------------------------------------------------------------------------------

-- | A literal value.
data Literal
  = LitInt !Integer !(Maybe (Int, IntFormat))  -- ^ Integer with optional bit-width and format
  | LitFloat !Double                           -- ^ Floating-point
  | LitChar !Char                              -- ^ Character
  | LitString !Text                            -- ^ String
  deriving stock (Eq, Show, Generic)

-- | Integer literal format.
data IntFormat
  = IntDec   -- ^ Decimal
  | IntHex   -- ^ Hexadecimal
  | IntBin   -- ^ Binary
  | IntOct   -- ^ Octal
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Operators
--------------------------------------------------------------------------------

-- | An operator (symbolic or backtick-quoted identifier).
data Op
  = OpSym !Text                     -- ^ Symbolic operator
  | OpIdent !(Located QualIdent)    -- ^ Backtick-quoted identifier (possibly qualified)
  deriving stock (Eq, Show, Generic)

-- | Operator fixity (associativity).
data FixityDir
  = InfixL   -- ^ Left-associative
  | InfixR   -- ^ Right-associative
  | InfixN   -- ^ Non-associative
  deriving stock (Eq, Show, Generic)

-- | Fixity with precedence level.
data Fixity = Fixity
  { fixDir   :: !FixityDir
  , fixPrec  :: !Int  -- ^ Precedence 0-9
  }
  deriving stock (Eq, Show, Generic)

-- | A fixity declaration.
data FixityDecl = FixityDecl
  { fixDeclFixity :: !Fixity
  , fixDeclOps    :: ![Located Op]
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Module/Interface/Rules
--------------------------------------------------------------------------------

-- | A statement in a module expression.
data ModuleStmt
  = MStmtBind !LPattern !(Maybe LType) !LExpr          -- ^ pat :: T <- mkFoo
  | MStmtLet ![LetItem]                                -- ^ let bindings
  | MStmtLetSeq ![LetItem]                             -- ^ letseq bindings
  | MStmtExpr !LExpr                                   -- ^ expression (for effects)
  | MStmtRules ![Located Rule]                         -- ^ addRules
  | MStmtInterface ![InterfaceField]                   -- ^ interface definition
  | MStmtTupleInterface ![LExpr]                       -- ^ interface (e1, e2, ...) tuple return
  | MStmtDef !LDefinition                              -- ^ BSV: local function/type definition in module
  deriving stock (Eq, Show, Generic)

-- | A field in an interface expression.
data InterfaceField = InterfaceField
  { ifSpan    :: !SrcSpan
  , ifName    :: !(Located Ident)
  , ifPats    :: ![LPattern]              -- ^ Method parameters
  , ifValue   :: !LExpr
  , ifWhen    :: !(Maybe Guard)           -- ^ Optional when-guard (e.g. enq x = f.enq x when f.notFull)
  }
  deriving stock (Eq, Show, Generic)

-- | A rule definition.
data Rule = Rule
  { ruleSpan    :: !SrcSpan
  , ruleName    :: !(Maybe LExpr)             -- ^ Optional rule name (any expression)
  , rulePragmas :: ![RulePragma]              -- ^ Rule pragmas
  , ruleCond    :: !(Maybe Guard)             -- ^ Optional condition (when), supports comma-separated conjuncts
  , ruleBody    :: !LExpr                     -- ^ Rule body (action)
  }
  deriving stock (Eq, Show, Generic)

-- | A pragma for rules.
data RulePragma
  = RPNoImplicitConditions
  | RPFireWhenEnabled
  | RPCanScheduleFirst
  | RPClockCrossingRule
  | RPDoc !Text
  deriving stock (Eq, Show, Generic)

-- | A pragma for methods/fields.
data MethodPragma
  = MPAlwaysReady
  | MPAlwaysEnabled
  | MPEnabled !LExpr           -- ^ enabled = <expr> (condition when method is enabled)
  | MPReady !LExpr             -- ^ ready = <expr> (condition when method is ready)
  | MPPrefixPort !Text         -- ^ prefix = "string" (port name prefix)
  | MPResultPort !Text         -- ^ result = "string" (result port name)
  | MPEnablePort !Text         -- ^ enable = "string" (enable port name)
  | MPReadyPort !Text          -- ^ ready = "string" (ready port name, when string not expr)
  | MPArgNames ![Text]         -- ^ arg_names = [name, ...] (argument port names)
  | MPDoc !Text
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Verilog Module Types
--------------------------------------------------------------------------------

-- | A method definition in a Verilog module.
data VerilogMethod = VerilogMethod
  { vmFieldId   :: !(Located Ident)   -- ^ Field/method name
  , vmMult      :: !(Maybe Int)       -- ^ Optional multiplicity [n]
  , vmPorts     :: ![PortSpec]        -- ^ Port specifications
  }
  deriving stock (Eq, Show, Generic)

-- | A port specification in a Verilog method.
data PortSpec = PortSpec
  { psName  :: !Text                  -- ^ Port name (string literal)
  , psProps :: ![PortProp]            -- ^ Port properties
  }
  deriving stock (Eq, Show, Generic)

-- | Port properties for Verilog modules.
data PortProp
  = PPReg                             -- ^ {reg}
  | PPConst                           -- ^ {const}
  | PPUnused                          -- ^ {unused}
  | PPInHigh                          -- ^ {inhigh}
  deriving stock (Eq, Show, Generic)

-- | Scheduling information for a Verilog module.
newtype SchedInfo = SchedInfo
  { schedEntries :: [SchedEntry]
  }
  deriving stock (Eq, Show, Generic)

-- | A scheduling entry.
data SchedEntry = SchedEntry
  { seLeft  :: ![Located Ident]       -- ^ Left methods
  , seOp    :: !SchedOp               -- ^ Scheduling operator
  , seRight :: ![Located Ident]       -- ^ Right methods
  }
  deriving stock (Eq, Show, Generic)

-- | Scheduling operators (any operator symbol is allowed).
type SchedOp = Text

--------------------------------------------------------------------------------
-- Located type aliases
--------------------------------------------------------------------------------

type LIdent = Located Ident
