{-# LANGUAGE TemplateHaskell #-}
-- | Embedded JavaScript for client-side symbol search.
module Language.Bluespec.DocGen.JS
  ( searchScript
  ) where

import Data.FileEmbed (embedFile)
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8)

-- | Vanilla-JS symbol search and anchor-link handler.
searchScript :: Text
searchScript = decodeUtf8 $(embedFile "data/search.js")
