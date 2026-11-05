-- Required by `cabal check` for `build-type: Hooks`.
import Distribution.Simple (defaultMainWithSetupHooks)
import SetupHooks (setupHooks)

main :: IO ()
main = defaultMainWithSetupHooks setupHooks
