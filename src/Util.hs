{-# LANGUAGE MagicHash, UnboxedTuples #-}

module Util where


import qualified GHC.Exts as E
import qualified Foreign as F

unsafeSizeof :: a -> Int
unsafeSizeof a =
  case E.unpackClosure# a of
    (# _, ptrs, nptrs #) ->
      F.sizeOf (undefined::Int) + -- one word for the header
        E.I# (E.sizeofByteArray# (E.unsafeCoerce# ptrs)
             E.+# E.sizeofByteArray# nptrs)