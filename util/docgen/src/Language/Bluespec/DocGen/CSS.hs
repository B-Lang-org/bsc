{-# LANGUAGE TemplateHaskell #-}
-- | Embedded stylesheet for the generated documentation.
module Language.Bluespec.DocGen.CSS
  ( stylesheet
  ) where

import Data.FileEmbed (embedFile)
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8)

-- | The single CSS file used across all generated HTML pages.
stylesheet :: Text
stylesheet = decodeUtf8 $(embedFile "data/docgen.css")
