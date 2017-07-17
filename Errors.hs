module Errors where

------------------------------------------------------------------------
-- TypeException handles error data & handling                        --
------------------------------------------------------------------------
data TypeException = NonEmptyCtxError
                   | EmptyCtxError
                   | InvalidContextError
                   | VarException
                   | AppSrcError
                   | InvalidArgError
                   | InvalidTypeError
