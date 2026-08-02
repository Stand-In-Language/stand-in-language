-- |Transitional re-export facade over the IR vocabulary modules. This
-- module is deleted at the end of the compiler-stages refactor; import the
-- Telomare.IR.* modules (and Telomare.Error) directly instead.
module Telomare
  ( module Telomare.Error
  , module Telomare.IR.Base
  , module Telomare.IR.Builder
  , module Telomare.IR.Core
  , module Telomare.IR.Loc
  , module Telomare.IR.Surface
  , module Telomare.IR.Types
  ) where

import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
