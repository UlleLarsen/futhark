{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

-- | A simple representation with SOACs and nested parallelism.
module Futhark.IR.SOACS
  ( SOACS,
    usesAD,

    -- * Module re-exports
    module Futhark.IR.Prop,
    module Futhark.IR.Traversals,
    module Futhark.IR.Pretty,
    module Futhark.IR.Syntax,
    module Futhark.IR.SOACS.SOAC,
  )
where

import Futhark.Builder
import Futhark.Construct
import Futhark.IR.Pretty
import Futhark.IR.Prop
import Futhark.IR.SOACS.SOAC
import Futhark.IR.Syntax
import Futhark.IR.Traversals
import qualified Futhark.IR.TypeCheck as TC

-- | The rep for the basic representation.
data SOACS

instance RepTypes SOACS where
  type Op SOACS = SOAC SOACS

instance ASTRep SOACS where
  expTypesFromPat = pure . expExtTypesFromPat

instance TC.CheckableOp SOACS where
  checkOp = typeCheckSOAC

instance TC.Checkable SOACS

instance Buildable SOACS where
  mkBody = Body ()
  mkExpPat merge _ = basicPat merge
  mkExpDec _ _ = ()
  mkLetNames = simpleMkLetNames

instance BuilderOps SOACS

instance PrettyRep SOACS

usesAD :: Prog SOACS -> Bool
usesAD prog = any stmUsesAD (progConsts prog) || any funUsesAD (progFuns prog)
  where
    funUsesAD = bodyUsesAD . funDefBody
    bodyUsesAD = any stmUsesAD . bodyStms
    stmUsesAD = expUsesAD . stmExp
    lamUsesAD = bodyUsesAD . lambdaBody
    expUsesAD (Op JVP {}) = True
    expUsesAD (Op VJP {}) = True
    expUsesAD (Op (Stream _ _ _ _ lam)) = lamUsesAD lam
    expUsesAD (Op (Screma _ _ (ScremaForm scans reds lam))) =
      lamUsesAD lam
        || any (lamUsesAD . scanLambda) scans
        || any (lamUsesAD . redLambda) reds
    expUsesAD (Op (Hist _ _ ops lam)) =
      lamUsesAD lam || any (lamUsesAD . histOp) ops
    expUsesAD (Op (Scatter _ _ lam _)) =
      lamUsesAD lam
    expUsesAD (If _ tbody fbody _) = bodyUsesAD tbody || bodyUsesAD fbody
    expUsesAD (DoLoop _ _ body) = bodyUsesAD body
    expUsesAD (WithAcc _ lam) = lamUsesAD lam
    expUsesAD BasicOp {} = False
    expUsesAD Apply {} = False
