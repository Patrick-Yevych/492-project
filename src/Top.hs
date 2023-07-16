import Eval
import Lang
import Norm
import Type

toplevel :: Ctx -> Toplevel -> Either Message ([Output], Ctx)
toplevel ctx (Define x e) =
  case lookupType ctx x of
    Right _ -> failure ("The name " ++ show x ++ " is already defined.")
    Left _ -> do
      t <- synth ctx e
      let v = eval (mkEnv ctx) initDlt e id
      return ([], define ctx x t v)
toplevel ctx (Example e) = do
  t <- synth ctx e
  let v = eval (mkEnv ctx) initDlt e id
      e' = readBackTyped ctx t v
      t' = readBackTyped ctx VU t
  return ([ExampleOutput (The t' e')], ctx)