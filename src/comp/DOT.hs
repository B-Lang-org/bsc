module DOT ( DOTGraph(..),
             DOTStmt(..),

             NodeAttr(..),
             NodeShape(..),
             NodeStyle(..),

             EdgeAttr(..),
             EdgeStyle(..),
             EdgeDir(..),

             GraphAttr(..),

             printDOTGraph
           ) where

import Data.List

import Util
import ErrorUtil


data DOTGraph = DOTGraph {
                  strict :: Bool,
                  digraph :: Bool,
                  graphId :: Maybe String,
                  stmts :: [DOTStmt]
                };

data DOTStmt = Node String [NodeAttr]
             -- XXX edges can also link subgraphs, not just node Ids
             | Edge [String] [EdgeAttr]
             | NodeAttr [NodeAttr]
             | EdgeAttr [EdgeAttr]
             | SubgraphAttr [GraphAttr]
             | GraphAttr GraphAttr
             -- XXX: Subgraph

-- XXX mode attributes
data NodeAttr = NLabel String
              | NShape NodeShape
              | NStyle NodeStyle
              -- FillColor
              -- Color

-- XXX more shapes
data NodeShape = NBox
               | NEllipse

-- XXX share the common styles with EdgeStyle?
data NodeStyle = -- line boundary
                 NSolid
               | NDashed
               | NDotted
               | NBold
               | NInvis
               -- others
               | NFilled
               | NDiagonals
               | NRounded

-- XXX more edge attributes
data EdgeAttr = ELabel String
              | EWeight Int
              | EStyle EdgeStyle
              | EDir EdgeDir
              -- XXX we should enforce that colors are either an RGB triple
              -- XXX or a color name (as listed in appendix G of the "dot" UG)
              | EColor String

data EdgeStyle = ESolid
               | EDashed
               | EDotted
               | EBold
               | EInvis

data EdgeDir = EForward
             | EBack
             | EBoth
             | ENone

-- XXX more graph attributes
data GraphAttr = GLabel String
               | GSize Int Int


-- XXX should there be a check function which checks that Ids and labels
-- XXX contain only the legal characters (spaces in labels need to be
-- XXX escaped, for example) and that the edge list has at least 2 elements
-- XXX etc?

printDOTGraph :: DOTGraph -> String
printDOTGraph (DOTGraph strict di gid stmts) =
    -- first line
    (if strict then "strict " else "") ++
    (if di then "digraph" else "graph") ++ " " ++
    (case gid of
         Nothing -> ""
         Just i -> "\"" ++ i ++ "\" "
    ) ++
    "{\n" ++
    -- stmts
    concat (intersperse ";\n" (map (printDOTStmt di) stmts)) ++
    -- closing
    "\n}\n"

printDOTStmt :: Bool -> DOTStmt -> String
printDOTStmt _ (Node i attrs) =
    i ++
    (if (null attrs)
     then ""
     else " " ++ printNodeAttrs attrs
    )
printDOTStmt di (Edge es attrs) =
    -- XXX assert that length "es" > 1?
    let op = if di then "->" else "--"
    in  concat (intersperse op es) ++
        (if (null attrs)
         then ""
         else " " ++ printEdgeAttrs attrs
        )
printDOTStmt _ (NodeAttr attrs) =
    if (null attrs)
    then internalError "printDOTStmt: null node attributes"
    else "node " ++ printNodeAttrs attrs
printDOTStmt _ (EdgeAttr attrs) =
    if (null attrs)
    then internalError "printDOTStmt: null edge attributes"
    else "edge " ++ printEdgeAttrs attrs
printDOTStmt _ (SubgraphAttr attrs) =
    if (null attrs)
    then internalError "printDOTStmt: null graph attributes"
    else "graph " ++ printGraphAttrs attrs
printDOTStmt _ (GraphAttr attr) =
    printGraphAttr attr

printNodeAttrs :: [NodeAttr] -> String
printNodeAttrs attrs =
    "[" ++ concat (intersperse ", " (map printNodeAttr attrs)) ++ "]"

printNodeAttr :: NodeAttr -> String
printNodeAttr (NLabel s) = "label=" ++ s
printNodeAttr (NShape s) = "shape=" ++ printNodeShape s
printNodeAttr (NStyle s) = "style=" ++ printNodeStyle s

printNodeShape :: NodeShape -> String
printNodeShape NBox = "box"
printNodeShape NEllipse = "ellipse"

printNodeStyle :: NodeStyle -> String
printNodeStyle NSolid     = "solid"
printNodeStyle NDashed    = "dashed"
printNodeStyle NDotted    = "dotted"
printNodeStyle NBold      = "bold"
printNodeStyle NInvis     = "invis"
printNodeStyle NFilled    = "filled"
printNodeStyle NDiagonals = "diagonals"
printNodeStyle NRounded   = "rounded"

printEdgeAttrs :: [EdgeAttr] -> String
printEdgeAttrs attrs =
    "[" ++ concat (intersperse ", " (map printEdgeAttr attrs)) ++ "]"

printEdgeAttr :: EdgeAttr -> String
printEdgeAttr (ELabel s) = "label=" ++ s
printEdgeAttr (EWeight n) = "weight=" ++ itos n
printEdgeAttr (EStyle s) = "style=" ++ printEdgeStyle s
printEdgeAttr (EDir d) = "dir=" ++ printEdgeDir d
printEdgeAttr (EColor c) = "color=" ++ c

printEdgeStyle :: EdgeStyle -> String
printEdgeStyle ESolid  = "solid"
printEdgeStyle EDashed = "dashed"
printEdgeStyle EDotted = "dotted"
printEdgeStyle EBold   = "bold"
printEdgeStyle EInvis  = "invis"

printEdgeDir :: EdgeDir -> String
printEdgeDir EForward = "forward"
printEdgeDir EBack    = "back"
printEdgeDir EBoth    = "both"
printEdgeDir ENone    = "none"

printGraphAttrs :: [GraphAttr] -> String
printGraphAttrs attrs =
    "[" ++ concat (intersperse ", " (map printGraphAttr attrs)) ++ "]"

printGraphAttr :: GraphAttr -> String
-- XXX check that the label is properly quoted and escaped if necessary?
-- XXX (cannot contain newlines, etc)
printGraphAttr (GLabel s) = "label=" ++ s
printGraphAttr (GSize x y) = "size=" ++ doubleQuote (itos x ++ "," ++ itos y)
