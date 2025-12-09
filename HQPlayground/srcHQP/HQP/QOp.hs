module HQP.QOp( 
    module HQP.QOp.Syntax,
    module HQP.QOp.Simplify,
    module HQP.QOp.HelperFunctions,
  -- re-export the *module names* for users to import qualified if they want semantics:
    module HQP.QOp.MatrixSemantics,     -- exported for convenience, see usage below
    module HQP.QOp.TensorSemantics,
    module HQP.QOp.StabilizerSemantics
  ) where

import HQP.QOp.Syntax
import HQP.QOp.Simplify
import HQP.QOp.HelperFunctions

-- Re-export the semantics modules so users may import them directly.
import qualified HQP.QOp.MatrixSemantics     as MatSem   
import qualified HQP.QOp.TensorSemantics     as TenSem
import qualified HQP.QOp.StabilizerSemantics as StabSem

-- To re-export the modules themselves (not their identifiers), add plain imports too:
import HQP.QOp.MatrixSemantics     ()
import HQP.QOp.TensorSemantics     ()
import HQP.QOp.StabilizerSemantics ()
