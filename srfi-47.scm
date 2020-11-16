(module srfi-47 ()
  (import scheme)
  (import (chicken base))
  (import (chicken module))
  (import (chicken fixnum))

  (export make-array array-ref array-set! make-shared-array array?
         array-rank array-dimensions array-in-bounds? array-store
         at1 au8 au16 au32 au64 as8 as16 as32 as64 ar32 ar64)

  (include "srfi-47-impl.scm"))
