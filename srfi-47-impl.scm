;;;;"array.scm" Arrays for Scheme
; Copyright (C) 2001, 2003 Aubrey Jaffer
;
;Permission to copy this software, to modify it, to redistribute it,
;to distribute modified versions, and to use it for any purpose is
;granted, subject to the following restrictions and understandings.
;
;1.  Any copy made of this software must include this copyright notice
;in full.
;
;2.  I have made no warranty or representation that the operation of
;this software will be error-free, and I am under no obligation to
;provide any services, by way of maintenance, update, or otherwise.
;
;3.  In conjunction with products arising from the use of this
;material, there shall be no use of my name in any advertising,
;promotional, or sales literature without prior written consent in
;each case.

;;@code{(require 'array)}
;;@ftindex array

(declare
 (fixnum)
 (export make-array array-ref array-set! make-shared-array array?
	 array-rank array-dimensions array-in-bounds? array-store
	 at1 au8 au16 au32 au64 as8 as16 as32 as64 ar32 ar64) )

(define-record array shape scales offset store tmap)

(define array:shape
  (lambda (array)
    (or (and-let* ([tmap (find-t array)])
	  (list (list 0 (+ -1 ((vector-ref tmap 4) array)))) )
	(array-shape array))))

(define array:scales
  (lambda (obj)
    (or (and (find-t obj) '(1))
	(array-scales obj))))

(define array:store
  (lambda (obj)
    (or (and (find-t obj) obj)
	(array-store obj))))

(define array:offset
  (lambda (obj)
    (or (and (find-t obj) 0)
	(array-offset obj))))

(define array:construct make-array)
(define array:predicate? array?)

;;@args obj
;;Returns @code{#t} if the @1 is an array, and @code{#f} if not.
(define array?
  (lambda (obj) 
    (and (not (##sys#immediate? obj)) 
	 (or (string? obj)
	     (vector? obj)
	     (and (##sys#generic-structure? obj)
		  (memq (##sys#slot obj 0) '(u8vector u16vector s8vector s16vector u32vector s32vector f32vector f64vector)) )
	     (array:predicate? obj)))) )

;;@noindent
;;@emph{Note:} Arrays are not disjoint from other Scheme types.  Strings
;;and vectors also satisfy @code{array?}.  A disjoint array predicate can
;;be written:
;;
;;@example
;;(define (strict-array? obj)
;;  (and (array? obj) (not (string? obj)) (not (vector? obj))))
;;@end example

;;@body
;;Returns @code{#t} if @1 and @2 have the same rank and shape and the
;;corresponding elements of @1 and @2 are @code{equal?}.
;;
;;@example
;;(array=? (create-array '#(foo) 3 3)
;;         (create-array '#(foo) '(0 2) '(0 2)))
;;  @result{} #t
;;@end example
#;(define (array=? array1 array2)
  (and (equal? (array:shape array1) (array:shape array2))
       (equal? (array:store array1) (array:store array2))))

(define (array:dimensions->shape dims)
  (map (lambda (dim) (if (list? dim) dim (list 0 (+ -1 dim)))) dims))

;;@args prototype bound1 bound2 @dots{}
;;
;;Creates and returns an array of type @1 with dimensions @2, @3,
;;@dots{} and filled with elements from @1.  @1 must be an array,
;;vector, or string.  The implementation-dependent type of the returned
;;array will be the same as the type of @1; except if that would be a
;;vector or string with non-zero origin, in which case some variety of
;;array will be returned.
;;
;;If the @1 has no elements, then the initial contents of the returned
;;array are unspecified.  Otherwise, the returned array will be filled
;;with the element at the origin of @1.
(define (make-array prototype . dimensions)
  (define range2length (lambda (bnd) (- 1 (apply - bnd))))
  ;;(if (not (array? prototype)) (set! prototype (vector prototype)))
  (let* ((shape (array:dimensions->shape dimensions))
	 (dims (map range2length shape))
	 (tmap (find-t prototype))
	 (scales
	  (do ((dims (reverse (cdr dims)) (cdr dims))
	       (scls '(1) (cons (* (car dims) (car scls)) scls)))
	      ((null? dims) scls))))
    (array:construct
     shape
     scales
     (- (apply + (map * (map car shape) scales)))
     (if tmap
	 (case ((vector-ref tmap 4) prototype)
	   ((0) ((vector-ref tmap 3) (apply * dims)))
	   (else ((vector-ref tmap 3) (apply * dims) ((vector-ref tmap 1) prototype 0))))
	 (let ((pshape (array:shape prototype)))
	   (case (apply * (map range2length pshape))
	     ((0) (make-vector (apply * dims)))
	     (else (make-vector (apply * dims)
				(apply array-ref prototype
				       (map car pshape)))))) )
     (or tmap
	 (vector vector? vector-ref vector-set! make-vector vector-length) ) ) ) )

(define (find-t prototype)
  (let loop ([tmap typemap])
    (cond [(null? tmap) #f]
	  [((vector-ref (car tmap) 0) prototype) (car tmap)]
	  [else (loop (cdr tmap))] ) ) )

(define typemap
  (list (vector string? string-ref string-set! make-string string-length)
	(vector vector? vector-ref vector-set! make-vector vector-length)
	(vector u8vector? u8vector-ref u8vector-set! make-u8vector u8vector-length)
	(vector u16vector? u16vector-ref u16vector-set! make-u16vector u16vector-length)
	(vector u32vector? u32vector-ref u32vector-set! make-u32vector u32vector-length)
	(vector s8vector? s8vector-ref s8vector-set! make-s8vector s8vector-length)
	(vector s16vector? s16vector-ref s16vector-set! make-s16vector s16vector-length)
	(vector s32vector? s32vector-ref s32vector-set! make-s32vector s32vector-length)
	(vector f32vector? f32vector-ref f32vector-set! make-f32vector f32vector-length)
	(vector f64vector? f64vector-ref f64vector-set! make-f64vector f64vector-length)))
	   
;;@noindent
;;These functions return a prototypical uniform-array enclosing the
;;optional argument (which must be of the correct type).  If the
;;uniform-array type is supported by the implementation, then it is
;;returned; defaulting to the next larger precision type; resorting
;;finally to vector.

(define (make-prototype-checker name pred? creator)
  (lambda args
    (case (length args)
      ((1) (if (pred? (car args))
	       (creator (car args))
	       (error "incompatible type" name (car args))))
      ((0) (creator))
      (else (error "wrong number of args" name args)))))

(define (integer-bytes?? n)
  (lambda (obj)
    (and (integer? obj)
	 (exact? obj)
	 (or (negative? n) (not (negative? obj)))
	 (do ((num obj (quotient num 256))
	      (n (+ -1 (abs n)) (+ -1 n)))
	     ((or (zero? num) (negative? n))
	      (zero? num))))))

#|
;;@args z
;;@args
;;Returns a high-precision complex uniform-array prototype.
(define Ac64 (make-prototype-checker 'ac64 complex? vector))
;;@args z
;;@args
;;Returns a complex uniform-array prototype.
(define Ac32 (make-prototype-checker 'ac32 complex? vector))
|#

(define as64 (make-prototype-checker 'as64 integer? vector))
(define au64 (make-prototype-checker 'au64 (lambda (x) (and (integer? x) (not (negative? x)))) vector))

;;@args x
;;@args
;;Returns a high-precision real uniform-array prototype.
(define ar64 (make-prototype-checker 'ar64 real? f64vector))
;;@args x
;;@args
;;Returns a real uniform-array prototype.
(define ar32 (make-prototype-checker 'ar32 real? f32vector))

;;@args n
;;@args
;;Returns an exact signed integer uniform-array prototype with at least
;;64 bits of precision.
;(define as64 (make-prototype-checker 'as64 (integer-bytes?? -8) vector))
;;@args n
;;@args
;;Returns an exact signed integer uniform-array prototype with at least
;;32 bits of precision.
(define as32 (make-prototype-checker 'as32 (integer-bytes?? -4) s32vector))
;;@args n
;;@args
;;Returns an exact signed integer uniform-array prototype with at least
;;16 bits of precision.
(define as16 (make-prototype-checker 'as16 (integer-bytes?? -2) s16vector))
;;@args n
;;@args
;;Returns an exact signed integer uniform-array prototype with at least
;;8 bits of precision.
(define as8 (make-prototype-checker 'as8 (integer-bytes?? -1) s8vector))

;;@args k
;;@args
;;Returns an exact non-negative integer uniform-array prototype with at
;;least 64 bits of precision.
;(define Au64 (make-prototype-checker 'au64 (integer-bytes?? 8) vector))
;;@args k
;;@args
;;Returns an exact non-negative integer uniform-array prototype with at
;;least 32 bits of precision.
(define au32 (make-prototype-checker 'au32 (integer-bytes?? 4) u32vector))
;;@args k
;;@args
;;Returns an exact non-negative integer uniform-array prototype with at
;;least 16 bits of precision.
(define au16 (make-prototype-checker 'au16 (integer-bytes?? 2) u16vector))
;;@args k
;;@args
;;Returns an exact non-negative integer uniform-array prototype with at
;;least 8 bits of precision.
(define au8 (make-prototype-checker 'au8 (integer-bytes?? 1) u8vector))

;;@args bool
;;@args
;;Returns a boolean uniform-array prototype.
(define at1
  (make-prototype-checker
   'at1 boolean? vector) )

;;@noindent
;;When constructing an array, @var{bound} is either an inclusive range of
;;indices expressed as a two element list, or an upper bound expressed as
;;a single integer.  So
;;
;;@example
;;(create-array '#(foo) 3 3) @equiv{} (create-array '#(foo) '(0 2) '(0 2))
;;@end example

;;@args array mapper bound1 bound2 @dots{}
;;@0 can be used to create shared subarrays of other
;;arrays.  The @var{mapper} is a function that translates coordinates in
;;the new array into coordinates in the old array.  A @var{mapper} must be
;;linear, and its range must stay within the bounds of the old array, but
;;it can be otherwise arbitrary.  A simple example:
;;
;;@example
;;(define fred (create-array '#(#f) 8 8))
;;(define freds-diagonal
;;  (make-shared-array fred (lambda (i) (list i i)) 8))
;;(array-set! freds-diagonal 'foo 3)
;;(array-ref fred 3 3)
;;   @result{} FOO
;;(define freds-center
;;  (make-shared-array fred (lambda (i j) (list (+ 3 i) (+ 3 j)))
;;                     2 2))
;;(array-ref freds-center 0 0)
;;   @result{} FOO
;;@end example
(define (make-shared-array array mapper . dimensions)
  (define odl (array:scales array))
  (define rank (length dimensions))
  (define shape (array:dimensions->shape dimensions))
  (do ((idx (+ -1 rank) (+ -1 idx))
       (uvt (append (cdr (vector->list (make-vector rank 0))) '(1))
	    (append (cdr uvt) '(0)))
       (uvts '() (cons uvt uvts)))
      ((negative? idx)
       (let* ((ker0 (apply + (map * odl (apply mapper uvt))))
	      (scales (map (lambda (uvt)
			     (- (apply + (map * odl (apply mapper uvt))) ker0))
			   uvts)))
	 (array:construct
	  shape
	  scales
	  (- (apply + (array:offset array)
		    (map * odl (apply mapper (map car shape))))
	     (apply + (map * (map car shape) scales)))
	  (array:store array)
	  (array-tmap array))))))

;;@body
;;Returns the number of dimensions of @1.  If @1 is not an array, 0 is
;;returned.
(define (array-rank obj)
  (if (array? obj) (length (array:shape obj)) 0))

;;@args array
;;Returns a list of inclusive bounds.
;;
;;@example
;;(array-shape (create-array '#() 3 5))
;;   @result{} ((0 2) (0 4))
;;@end example
;(define array-shape array:shape)

;;@body
;;@code{array-dimensions} is similar to @code{array-shape} but replaces
;;elements with a 0 minimum with one greater than the maximum.
;;
;;@example
;;(array-dimensions (create-array '#() 3 5))
;;   @result{} (3 5)
;;@end example
(define (array-dimensions array)
  (map (lambda (bnd) (if (zero? (car bnd)) (+ 1 (cadr bnd)) bnd))
       (array:shape array)))

(define (array:in-bounds? array indices)
  (do ((bnds (array:shape array) (cdr bnds))
       (idxs indices (cdr idxs)))
      ((or (null? bnds)
	   (null? idxs)
	   (not (integer? (car idxs)))
	   (not (<= (caar bnds) (car idxs) (cadar bnds))))
       (and (null? bnds) (null? idxs)))))

;;@args array index1 index2 @dots{}
;;Returns @code{#t} if its arguments would be acceptable to
;;@code{array-ref}.
(define (array-in-bounds? array . indices)
  (array:in-bounds? array indices))

;;@args array index1 index2 @dots{}
;;Returns the (@2, @3, @dots{}) element of @1.
(define (array-ref array . indices)
  (define store (array:store array))
  (or (array:in-bounds? array indices)
      (error 'array-ref "bad indices" indices))
  ((vector-ref (array-tmap array) 1)
   store (apply + (array:offset array) (map * (array:scales array) indices))))

;;@args array obj index1 index2 @dots{}
;;Stores @2 in the (@3, @4, @dots{}) element of @1.  The value returned
;;by @0 is unspecified.
(define (array-set! array obj . indices)
  (define store (array:store array))
  (or (array:in-bounds? array indices)
      (error 'array-set! "bad indices" indices))
  ((vector-ref (array-tmap array) 2)
   store (apply + (array:offset array) (map * (array:scales array) indices))
   obj))

#|
(define fred (make-array '#(#f) 8 8))
(define freds-diagonal
  (make-shared-array fred (lambda (i) (list i i)) 8))
(array-set! freds-diagonal 'foo 3)
(print (array-ref fred 3 3))
(define freds-center
  (make-shared-array fred (lambda (i j) (list (+ 3 i) (+ 3 j)))
                     2 2))
(print (array-ref freds-center 0 0))
|#
