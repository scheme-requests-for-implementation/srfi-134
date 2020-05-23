#!/usr/bin/env bash
# -*- wisp -*-
if ! guile -L $(dirname $(realpath "$0")) -C $(dirname $(realpath "$0")) --language=wisp -c '' 2>/dev/null; then
    guile -L $(dirname $(realpath "$0")) -C $(dirname $(realpath "$0")) -c '(import (language wisp) (language wisp spec))' >/dev/null 2>&1
fi
PROG="$0"
if [[ "$1" == "-i" ]]; then
    shift
    exec -a "${PROG}" guile -L $(dirname $(realpath "$0")) -C $(dirname $(realpath "$0")) --language=wisp -x .w -e '(deque)' -- "${@}"
else
    exec -a "${PROG}" guile -L $(dirname $(realpath "$0")) -C $(dirname $(realpath "$0")) --language=wisp -x .w -e '(deque)' -c '' "${@}" 2>/dev/null || (echo "${PROG} died" >2 && false)
fi
; !#

;; deque.w --- immutable deques for Guile following srfi-134

;; Copyright (C) 2020 Arne Babenhauserheide <arne_bab@web.de>

;; Author: Arne Babenhauserheide <arne_bab@web.de>

;; This library is free software; you can redistribute it and/or
;; modify it under the terms of the GNU Lesser General Public
;; License as published by the Free Software Foundation; either
;; version 3 of the License, or (at your option) any later version.

;; This library is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; Lesser General Public License for more details.

;; You should have received a copy of the GNU Lesser General Public
;; License along with this library. If not, see
;; <http://www.gnu.org/licenses/>.


;; for emacs (progn (defun test-this-file () (interactive) (save-buffer) (shell-command (concat (buffer-file-name (current-buffer)) " --test"))) (local-set-key (kbd "<f9>") 'test-this-file))

;; this is a partial, simpler implementation of SRFI-134, also based on two lists but with fewer operations per action and fewer optimizations. This implementation is not balancing and ideque-front and ideque-back only takes amortized O(1) time. See https://srfi.schemers.org/srfi-134/


;; Docstrings of the procedures are taken from
;; https://srfi.schemers.org/srfi-134/srfi-134.html and Copyright (C)
;; John Cowan, Kevin Wortman (2015). All Rights Reserved.

;; Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
;;
;; The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
;;
;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.


;; TODO: Ensure that it is not possible to reach states with exported
;; commands that require expensive balancing on addition.


define-module : deque
    . #:export
    main
      ;; SRFI 134 operations
      ;; Constructors
      . ideque ideque-tabulate ideque-unfold ideque-unfold-right
      ;; Predicates
      . ideque? ideque-empty? ideque= ideque-any ideque-every
      ;; Queue operations
      . ideque-front ideque-back ideque-remove-front ideque-remove-back ideque-add-front ideque-add-back
      ;; Other accessors
      . ideque-ref ideque-take ideque-drop ideque-take-right ideque-drop-right ideque-split-at
      ;; Whole ideque
      . ideque-length ideque-append ideque-reverse ideque-count ideque-zip
      ;; Mapping
      . ideque-map ideque-filter-map ideque-for-each ideque-for-each-right ideque-fold ideque-fold-right ideque-append-map
      ;; Filtering
      . ideque-filter ideque-remove ideque-partition
      ;; Searching
      . ideque-find ideque-find-right
      ;; Conversion
      . ideque->list list->ideque ideque-take-while ideque-take-while-right ideque-drop-while ideque-drop-while-right ideque-span ideque-break
      ;; Extensions to SRFI-134
      . ideque-add-front! ideque-add-back! ideque-pop-front ideque-pop-back ideque-pop-front! ideque-pop-back!

import : ice-9 pretty-print
         srfi srfi-1
         srfi srfi-9
         srfi srfi-11 ;; let-values
         doctests
         only (rnrs io ports) eof-object eof-object?

define-record-type <ideque>
    make-ideque front back
    . ideque?
    front ideque-front-elements ideque-front-elements-set!
    back ideque-back-elements ideque-back-elements-set!

define : ideque-add/internal add-to other value
    if : not : null? other
        values
            cons value add-to
            . other
        cond
            : null? add-to
              ;; first element
              values
                  cons value add-to
                  . other
            : null? : cdr add-to
              ;; second element: just use the front as the back
              values
                  cons value other
                  . add-to
            else
                error "illegal state: other elements of ideque must never be null? when adding to an ideque with at least 2 elements, but elements are add-to ~s and other ~s, trying to add value ~s. This is a programming error, please report it!" add-to other value


define : ideque-add-front ideq value
    . "Returns an ideque with obj pushed to the front of ideque. Takes O(1) time. "
    let-values
        :
            : front back
              ideque-add/internal
                  ideque-front-elements ideq
                  ideque-back-elements ideq
                  . value
        make-ideque front back


define : ideque-add-front! ideq value
    . "Adds the obj to the front of ideque. Takes O(1) time. Mutates the ideque."
    ideque-front-elements-set! ideq : cons value : ideque-front-elements ideq

define : ideque-add-back! ideq value
    . "Adds the obj to the back of ideque. Takes O(1) time. Mutates the ideque."
    ideque-back-elements-set! ideq : cons value : ideque-back-elements ideq

define : ideque-add-back ideq value
    . "Returns an ideque with obj pushed to the back of ideque. Takes O(1) time. "
    let-values
        :
            : back front
              ideque-add/internal
                  ideque-back-elements ideq
                  ideque-front-elements ideq
                  . value
        make-ideque front back



define : ideque-remove/internal front back
    . "get the first value from the deque, shifting back to front if necessary.

       Returns the values front, back, and retrieved value."
    ##
        tests
            test-equal #f
                ideque-remove/internal '() '()
            test-equal '((b c) () a)
                let-values : : (front back value) : ideque-remove/internal '(a b c) '()
                    list front back value
            test-error
                let-values : : (front back value) : ideque-remove/internal '() '(c b a)
                    list front back value
            test-equal '(() () 0)
                let-values : : (front back value) : ideque-remove/internal '() '(0)
                    list front back value
            test-error
                let-values : : (front back value) : ideque-remove/internal '() '(1 0)
                    list front back value
            test-equal '((1) () 0)
                let-values : : (front back value) : ideque-remove/internal '(0) '(1)
                    list front back value
            test-equal '((1) (2) 0)
                let-values : : (front back value) : ideque-remove/internal '(0) '(2 1)
                    list front back value
            test-equal '((1 2) (3) 0)
                let-values : : (front back value) : ideque-remove/internal '(0) '(3 2 1)
                    list front back value
            test-equal '((1 2 3) (4) 0)
                let-values : : (front back value) : ideque-remove/internal '(0) '(4 3 2 1)
                    list front back value
            test-equal '((1 2 3) (5 4) 0)
                let-values : : (front back value) : ideque-remove/internal '(0) '(5 4 3 2 1)
                    list front back value
            test-equal '((1 2 3 4) (6 5) 0)
                let-values : : (front back value) : ideque-remove/internal '(0) '(6 5 4 3 2 1)
                    list front back value
            test-equal '((1 2 3 4 5) (7 6) 0)
                let-values : : (front back value) : ideque-remove/internal '(0) '(7 6 5 4 3 2 1)
                    list front back value
            test-equal '((1 2 3 4 5) (8 7 6) 0)
                let-values : : (front back value) : ideque-remove/internal '(0) '(8 7 6 5 4 3 2 1)
                    list front back value
            test-equal '((1 2 3 4 5 6) (9 8 7) 0)
                let-values : : (front back value) : ideque-remove/internal '(0) '(9 8 7 6 5 4 3 2 1)
                    list front back value
    cond
        ;; error: deque is empty. Signal the error with #f
        : and (null? back) : null? front
          values #f #f #f
        ;; front is empty. Remove the last element from the back. This can only happen if at most 1 element remains in the deque.
        : null? front
          if : not : null? : cdr back
               error "illegal state: back elements of ideque with empty front must hold at most 1 element when removing an element from front, but elements are front ~s and back ~s. This is a programming error, please report it!" front back
               values '() '() : car back
        ;; remove the last element from front
        : and (null? back) : null? : cdr front
          values '() '() : car front
        ;; balance the deque instead of removing the last element from front when more than one element remains in the back
        : null? : cdr front
          let loop : (count 0) (reversed '()) (back back)
              if : null? : cdr back
                   cond
                       : = count 0 ;; there was only one element in the back, shift to the front
                         values back '() : car front
                       : = count 1 ;; there were two elements in the back, reversed holds the first back element, the back holds what’s the new front. No further splitting necessary
                         values back reversed : car front
                       else
                         ;; move only 2/3rd of the reversed list to
                         ;; the front to prevent worst-case O(N²) when
                         ;; alternating between front and back; needs
                         ;; a let loop to track the length while
                         ;; reversing. This doubles the cost of
                         ;; removing, but keeps the amortized cost
                         ;; constant for the worst case access pattern
                         ;; of alternating front-and-back.
                         let-values : : (new-front new-back-reversed) : split-at reversed : floor/ (* count 2) 3
                             values
                                 cons (car back) new-front
                                 reverse new-back-reversed
                                 car front
                   loop
                       + count 1
                       cons (car back) reversed
                       cdr back
        else
            values : cdr front
                     . back
                     car front

define : ideque-remove-front ideq
    . "Returns an ideque with the front element of ideque removed. It is an error for ideque to be empty. Takes O(1) time."
    ##
        tests
            test-equal : ideque '()
                ideque-remove-front : make-ideque '(1) '()
            test-equal : ideque '()
                ideque-remove-front : make-ideque '() '(1)
            test-equal '(2)
                ideque->list : ideque-remove-front : make-ideque '(1) '(2)
            test-equal '(2)
                ideque->list : ideque-remove-front : ideque '(1 2)
            test-equal '(2 3)
                ideque->list : ideque-remove-front : make-ideque '(1) '(3 2)
            test-equal '(2 3)
                ideque->list : ideque-remove-front : make-ideque '(1 2) '(3)
            test-error
                ideque-remove-front : ideque '()
    define-values : front back value
        ideque-remove/internal
            ideque-front-elements ideq
            ideque-back-elements ideq
    if : not front
       error "Empty deque:" ideq
       make-ideque front back

define : ideque-remove-back ideq
    . "Returns an ideque with the back element of ideque removed. It is an error for ideque to be empty. Takes O(1) time."
    ##
        tests
            test-equal : ideque '()
                ideque-remove-back : make-ideque '(1) '()
            test-equal : ideque '()
                ideque-remove-back : make-ideque '() '(1)
            test-equal '(1 2)
                ideque->list : ideque-remove-back : make-ideque '(1) '(3 2)
            test-equal '(1 2)
                ideque->list : ideque-remove-back : make-ideque '(1 2) '(3)
            test-equal '(1)
                ideque->list : ideque-remove-back : make-ideque '(1) '(2)
            test-error
                ideque-remove-back : ideque '()
    define-values : back front value
        ideque-remove/internal
            ideque-back-elements ideq
            ideque-front-elements ideq
    if : not front
       error "Empty deque:" ideq
       make-ideque front back



define : ideque-front ideq
    ##
        tests
            test-error
                ideque-front : make-ideque '() '()
    define front : ideque-front-elements ideq
    if : null? front
         let : : back : ideque-back-elements ideq
             if : null? back
                 error "Empty deque:" ideq
                 first : take-right back 1
         first front


define : ideque-back ideq
    ##
        tests
            test-error
                ideque-back : make-ideque '() '()
    define back : ideque-back-elements ideq
    if : null? back
         let : : front : ideque-front-elements ideq
             if : null? front
                 error "Empty deque:" ideq
                 first : take-right front 1
         first back

define : ideque->list ideq
    ##
        tests
            test-equal : list 1 2 3
                ideque->list : ideque '(1 2 3)
    append : ideque-front-elements ideq
             reverse : ideque-back-elements ideq

define : list->ideque l
    ideque l

define : ideque elements
    . "Returns an ideque containing the elements. The first element (if any) will be at the front of the ideque and the last element (if any) will be at the back. Takes O(n) time, where n is the number of elements. "
    ##
        tests
            ;; One element is in front, rest is in the back to avoid
            ;; O(N) access to the front, if elements are repeatedly
            ;; added to the back and the front is only accessed but
            ;; never removed
            test-equal '(World)
                  ideque-back-elements : ideque '(Hello World)
            test-equal '()
                  ideque-back-elements : ideque '()
            test-equal '(3 2)
                  ideque-back-elements : ideque '(1 2 3)
            test-equal '(1)
                  ideque-front-elements : ideque '(1 2 3)
            test-equal '(2)
                  ideque-back-elements : ideque '(1 2)
            test-equal '(1)
                  ideque-front-elements : ideque '(1 2)
    if : null? elements
        make-ideque '() '()
        make-ideque
            list : car elements
            reverse : cdr elements

define : ideque-tabulate n proc
    . " Invokes the predicate proc on every exact integer from 0 (inclusive) to n (exclusive). Returns an ideque containing the results in order of generation. Takes O(n) time. "
    ##
        tests
            test-equal : ideque '(0 1 2 3)
                ideque-tabulate 4 : λ(x) x
    ideque : map proc : iota n

define : ideque-unfold stop? mapper successor seed
    . "Invokes the predicate stop? on seed. If it returns false, generate the next result by applying mapper to seed, generate the next seed by applying successor to seed, and repeat this algorithm with the new seed. If stop? returns true, return an ideque containing the results in order of accumulation. Takes O(n) time. "
    ##
        tests
            test-equal : list 0 1 2 3
                ideque->list
                  ideque-unfold
                    λ(x) : > x 3
                    λ(x) x
                    λ(x) : + x 1
                    . 0
    let loop : (front '()) (elements-reverse '()) (seed seed)
        if : stop? seed
            make-ideque front elements-reverse
            ;; first put one element in front to ensure that with 2 or more elements there is no empty list.
            if : null? front
                loop : cons (mapper seed) front
                    . elements-reverse
                    successor seed
                loop front
                    cons (mapper seed) elements-reverse
                    successor seed

define : ideque-unfold-right stop? mapper successor seed
    . "Invokes the predicate stop? on seed. If it returns false, generate the next result by applying mapper to seed, generate the next seed by applying successor to seed, and repeat the algorithm with the new seed. If stop? returns true, return an ideque containing the results in reverse order of accumulation. Takes O(n) time."
    ##
        tests
            test-equal : list 3 2 1 0
                ideque->list
                  ideque-unfold-right
                    λ(x) : > x 3
                    λ(x) x
                    λ(x) : + x 1
                    . 0
    let loop : (elements-reverse '()) (seed seed)
        if : stop? seed
            ideque elements-reverse
            loop : cons (mapper seed) elements-reverse
                   successor seed

define : ideque-empty? ideq
    . "Returns #t if ideque contains zero elements, and #f otherwise. Takes O(1) time. "
    ##
        tests
            test-equal #t : ideque-empty? : ideque '()
            test-equal #f : ideque-empty? : ideque '(1)
            test-equal #t : ideque-empty? : make-ideque '() '()
            test-equal #f : ideque-empty? : make-ideque '(1) '()
            test-equal #f : ideque-empty? : make-ideque '() '(1)
            test-equal #f : ideque-empty? : make-ideque '(1) '(1)
    and : null? : ideque-front-elements ideq
          null? : ideque-back-elements ideq

define : ideque= elt= . ideques
    ##
        tests
            test-equal #f : ideque= = (ideque '(1 2)) (ideque '(1 3))
            test-equal #f : ideque= = (ideque '(1 2)) (ideque '(1))
    if
       or : null? ideques
            null? : cdr ideques
       . #t ;; zero or one ideques
       and
           let loop
               : elements1 : ideque->list : car ideques
                 elements2 : ideque->list : car : cdr ideques
               cond
                   : and (null? elements1) (null? elements2)
                     apply ideque= elt= : cdr ideques
                   : or (null? elements1) (null? elements2)
                     . #f
                   : elt= (car elements1) (car elements2)
                     loop (cdr elements1) (cdr elements2)
                   else
                     . #f

define : ideque-any pred ideq
    . "Invokes pred on the elements of the ideque in order until one call returns a true value, which is then returned. If there are no elements, returns #f. Takes O(n) time."
    ##
        tests
            test-equal #t : ideque-any zero? : ideque '(0 0 0)
            test-equal #t : ideque-any zero? : ideque '(0 1 0)
            test-equal #t : ideque-any zero? : ideque '(1 0)
            test-equal #f : ideque-any zero? : ideque '()
            test-equal #f : ideque-any zero? : ideque '(1)
            test-equal #f : ideque-any zero? : ideque '(1 1)
    if (ideque-empty? ideq) #f
      let loop
          : front : ideque-front-elements ideq
            back : ideque-back-elements ideq
          cond
              : and (null? front) (null? back)
                . #f
              : null? front
                loop (reverse back) front
              : pred : car front
                . #t
              else
                loop (cdr front) back

define : ideque-every pred ideq
    . "Invokes pred on the elements of the ideque in order until one call returns a false value, which is then returned. If there are no elements, returns #t. Takes O(n) time."
    ##
        tests
            test-equal #t : ideque-every zero? : ideque '(0 0 0)
            test-equal #f : ideque-every zero? : ideque '(0 1 0)
            test-equal #f : ideque-every zero? : ideque '(1 0)
            test-equal #t : ideque-every zero? : ideque '()
            test-equal #f : ideque-every zero? : ideque '(1)
            test-equal #f : ideque-every zero? : ideque '(1 1)
    if (ideque-empty? ideq) #t
      let loop
          : front : ideque-front-elements ideq
            back : ideque-back-elements ideq
          cond
              : and (null? front) (null? back)
                . #t
              : null? front
                loop (reverse back) front
              : pred : car front
                loop (cdr front) back
              else
                . #f

define : ideque-ref ideq n
    . "Returns the nth element of ideque. It is an error unless n is less than the length of ideque. Takes O(n) time."
    ##
        tests
            test-error : ideque-ref (ideque '()) 0
            test-equal 1 : ideque-ref (ideque '(1)) 0
            test-equal 'b : ideque-ref (ideque '(a b)) 1
            test-error : ideque-ref (ideque '(a b)) 2
    let loop : (q ideq) (n n)
        if : zero? n
             ideque-front q
             loop (ideque-remove-front q) (- n 1)


define : ideque-take ideq n
    . "Returns an ideque containing the first n elements of ideque. It is an error if n is greater than the length of ideque. Takes O(n) time."
    ##
        tests
            test-error : ideque-take (ideque '()) 1
            test-equal '() : ideque-take (ideque '(1)) 0
            test-equal '(a) : ideque-take (ideque '(a b)) 1
            test-error : ideque-take (ideque '(a b)) 3
    let loop : (q ideq) (n n) (res '())
        if : zero? n
             reverse! res
             loop
                 ideque-remove-front q
                 - n 1
                 cons (ideque-front q) res


define : ideque-take-right ideq n
    . "Returns an ideque containing the last n elements of ideque. It is an error if n is greater than the length of ideque. Takes O(n) time."
    ##
        tests
            test-error : ideque-take (ideque '()) 1
            test-equal '() : ideque-take-right (ideque '(1)) 0
            test-equal '(b) : ideque-take-right (ideque '(a b)) 1
            test-error : ideque-take (ideque '(a b)) 3
    let loop : (q ideq) (n n) (res '())
        if : zero? n
             reverse! res
             loop
                 ideque-remove-back q
                 - n 1
                 cons (ideque-back q) res


define : ideque-drop ideq n
    . "Returns an ideque containing all but the first n elements of ideque. It is an error if n is greater than the length of ideque. Takes O(n) time. "
    ##
        tests
            test-error : ideque-drop (ideque '()) 1
            test-equal '(1) : ideque->list : ideque-drop (ideque '(1)) 0
            test-equal '(b) : ideque->list : ideque-drop (ideque '(a b)) 1
            test-error : ideque-drop (ideque '(a b)) 3
    let loop : (q ideq) (n n)
        if : zero? n
             . q
             loop (ideque-remove-front q) (- n 1)


define : ideque-drop-right ideq n
    . "Returns an ideque containing all but the last n elements of ideque. It is an error if n is greater than the length of ideque. Takes O(n) time. "
    ##
        tests
            test-error : ideque-drop (ideque '()) 1
            test-equal '(1) : ideque->list : ideque-drop-right (ideque '(1)) 0
            test-equal '(a b) : ideque->list : ideque-drop-right (ideque '(a b c)) 1
            test-error : ideque-drop (ideque '(a b)) 3
    let loop : (q ideq) (n n)
        if : zero? n
             . q
             loop (ideque-remove-back q) (- n 1)


define : ideque-split-at ideq n
    . "Returns an ideque containing the first n elements of ideque. It is an error if n is greater than the length of ideque. Takes O(n) time."
    ##
        tests
            test-error : ideque-split-at (ideque '()) 1
            test-equal '() : ideque-split-at (ideque '(1)) 0
            test-equal '(a) : ideque-split-at (ideque '(a b c)) 1
            test-equal '(b c) : call-with-values (λ() (ideque-split-at (ideque '(a b c)) 1)) (λ(x y) y)
            test-error : ideque-split-at (ideque '(a b)) 3
    let loop : (q ideq) (n n) (res '())
        if : zero? n
             values
                 reverse! res
                 ideque->list q
             loop
                 ideque-remove-front q
                 - n 1
                 cons (ideque-front q) res


define : ideque-length ideq
    . "Returns the length of ideque as an exact integer. Takes O(n) time."
    ##
        tests
            test-equal 2 : ideque-length : ideque '(1 2)
            test-equal 3 : ideque-length : make-ideque '(1 2) '(1)
            test-equal 0 : ideque-length : ideque '()
    + : length : ideque-front-elements ideq
        length : ideque-back-elements ideq

define : ideque-append . ideqs
    . "Returns an ideque with the contents of the ideque followed by the others, or an empty ideque if there are none. Takes O(kn) time, where k is the number of ideques and n is the number of elements involved. For ideques that have all elements in the back elements, the time can be O(n - m), with m the elements in the last ideque, as for append."
    ##
        tests
            test-equal '() : ideque->list : ideque-append
            test-equal '(1) : ideque->list : ideque-append (ideque '(1))
            test-equal '(2 3 4) : ideque->list : ideque-remove-front : ideque-append (ideque '())  (ideque '(1 2 3 4))
            test-equal '(1 2 3) : ideque->list : ideque-append (ideque '(1 2 3))
            test-equal '(1 2 3) : ideque->list : ideque-append (make-ideque '(1) '(3 2))
            test-equal '(1 2 3 4) : ideque->list : ideque-append (make-ideque '(1) '(3 2)) (ideque '(4))
            test-equal '(1 2 3 4 5) : ideque->list : ideque-append (make-ideque '(1) '(3 2)) (ideque '(4 5))
            test-equal (iota 10) : ideque->list : apply ideque-append : map ideque : map list : iota 10
    cond
        : null? ideqs
          ideque '()
        : null? : cdr ideqs
          let : : ideq : car ideqs
            make-ideque
              ideque-front-elements ideq
              ideque-back-elements ideq
        else
            ;; ensure that if there is at least one non-empty ideque, at least one element is in the front
            let loop : (front (ideque-front-elements (car ideqs))) (back (ideque-back-elements (car ideqs))) (ideqs ideqs)
                cond
                    : and (null? front) (null? back)
                      loop
                          ideque-front-elements (car (cdr ideqs))
                          ideque-back-elements (car (cdr ideqs))
                          cdr ideqs
                    : and (null? front) (null? (cdr back))
                        ;; move the single back element to front: now whatever happens to back the ideque is legal
                        loop back front ideqs
                    : null? front
                      let : : back-reversed-without-first : reverse : cdr back
                          ;; the minimal legal ideque: keep one element in back, move the rest to front.
                          loop
                              . back-reversed-without-first
                              car back
                              . ideqs
                    else
                        ;; front is not null?, we just aggregate everything on back
                        make-ideque
                            . front
                            fold
                                λ : ideq elements ;; append takes time relative to the elements in all lists but the last
                                    append : ideque-back-elements ideq
                                        reverse : ideque-front-elements ideq
                                        . elements
                                ;; use the first ideq as initial elements to avoid one reversing and appending operation
                                . back
                                cdr ideqs


define : ideque-reverse ideq
    . "Returns an ideque containing the elements of ideque in reverse order. Takes O(1) time. "
    ##
        tests
            test-equal : ideque->list : ideque '(3 2 1)
                ideque->list : ideque-reverse : ideque '(1 2 3)
            test-equal : ideque->list : ideque '(x a v)
                ideque->list : ideque-reverse : ideque '(v a x)
    make-ideque
        ideque-back-elements ideq
        ideque-front-elements ideq

define : ideque-count pred ideq
    . "Pred is a procedure taking a single value and returning a single value. It is applied element-wise to the elements of ideque, and a count is tallied of the number of elements that produce a true value. This count is returned. Takes O(n) time. The dynamic order of calls to pred is unspecified."
    ##
        tests
            test-equal 3
                ideque-count zero? : ideque '(1 3 5 9 0 7 4 0 3 0)
            test-equal 2
                ideque-count even? : ideque '(1 2 3 4 5)
            test-equal 3
                ideque-count odd? : ideque '(1 2 3 4 5)
    define : add-one-if-true element count
        if : pred element
           + count 1
           . count
    +
        fold add-one-if-true 0 : ideque-front-elements ideq
        fold add-one-if-true 0 : ideque-back-elements ideq

define : ideque-zip . ideques
    . "Returns an ideque of lists (not ideques) each of which contains the corresponding elements of ideques in the order specified. Terminates when all the elements of any of the ideques have been processed. Takes O(kn) time, where k is the number of ideques and n is the number of elements in the shortest ideque."
    ##
        tests
            test-equal '((11 21) (12 22) (13 23))
                ideque->list
                    ideque-zip
                        ideque '(11 12 13)
                        ideque '(21 22 23)
    list->ideque : apply zip : map ideque->list ideques

define : make-balanced-ideque/internal front back
    . "create a legal ideque, moving elements between front and back if necessary to keep O(1) for all access patterns"
    ##
        tests
            test-equal
                make-ideque '(1) '(2)
                make-balanced-ideque/internal '() '(2 1)
            test-equal
                make-ideque '(1) '(2)
                make-balanced-ideque/internal '(1 2) '()
            test-equal ;; minimal safety
                make-ideque '(1) '(7 6 5 4 3 2)
                make-balanced-ideque/internal '(1 2 3 4 5 6 7) '()
            test-equal ;; minimal safety
                make-ideque '(1 2 3 4 5 6) '(7)
                make-balanced-ideque/internal '() '(7 6 5 4 3 2 1)
    cond
        : null? front
          cond
              ;; empty ideques stay unchanged
              : null? back
                make-ideque front back
              ;; single element ideques stay unchanged
              : null? : cdr back
                make-ideque front back
              ;; shift from back to front
              else
                make-ideque
                    reverse : cdr back
                    list : car back
        : null? back
          cond
              ;; empty ideques stay unchanged
              : null? front
                make-ideque front back
              ;; single element ideques stay unchanged
              : null? : cdr front
                make-ideque front back
              ;; shift from front to back
              else
                make-ideque
                    list : car front
                    reverse : cdr front
        ;; ideques without empty side stay unchanged
        else
          make-ideque front back


define-syntax-rule : ideque-operate-on-elements/internal ideq proc args ...
    make-balanced-ideque/internal
        proc args ... : ideque-front-elements ideq
        proc args ... : ideque-back-elements ideq

define-syntax-rule : ideque-operate-on-elements-right/internal ideq proc args ...
    make-balanced-ideque/internal
        proc args ... : ideque-back-elements ideq
        proc args ... : ideque-front-elements ideq

define : ideque-map proc ideq
    . "Applies proc to the elements of ideque and returns an ideque containing the results in order. The dynamic order of calls to proc is unspecified. Takes O(n) time."
    ##
        tests
            test-equal '(2 3 4)
                ideque->list
                    ideque-map 1+
                        ideque '(1 2 3)
    ideque-operate-on-elements/internal ideq map proc

define : ideque-filter-map proc ideq
    . "Applies proc to the elements of ideque and returns an ideque containing the true (i.e. non-#f) results in order. The dynamic order of calls to proc is unspecified. Takes O(n) time."
    ##
        tests
            test-equal '(4 8)
                ideque->list
                    ideque-filter-map
                        λ(x) : and (even? x) : * 2 x
                        ideque '(1 2 3 4)
    ideque-operate-on-elements/internal ideq filter-map proc

define : ideque-for-each proc ideq
    . "Applies proc to the elements of ideque in forward order and returns an unspecified result. Takes O(n) time."
    ##
        tests
            test-equal '(1 2 3)
                let : : l : list
                    ideque-for-each : λ(x) : set! l : cons x l
                        ideque '(1 2 3)
                    reverse l
    for-each proc : ideque-front-elements ideq
    for-each proc : reverse : ideque-back-elements ideq

define : ideque-for-each-right proc ideq
    . "Applies proc to the elements of ideque in reverse order and returns an unspecified result. Takes O(n) time."
    ##
        tests
            test-equal '(3 2 1)
                let : : l : list
                    ideque-for-each-right : λ(x) : set! l : cons x l
                        ideque '(1 2 3)
                    reverse l
    for-each proc : ideque-back-elements ideq
    for-each proc : reverse : ideque-front-elements ideq

define : ideque-fold proc nil ideq
    . "Invokes proc on the elements of ideque in forward order, passing the result of the previous invocation as a second argument. For the first invocation, nil is used as the second argument. Returns the result of the last invocation, or nil if there was no invocation. Takes O(n) time."
    ##
        tests
            test-equal : fold cons '() '(a b c)
                ideque-fold cons '() : ideque '(a b c)
            test-equal : fold cons '() '(a b c d e f)
                ideque-fold cons '() : make-ideque '(a b c) '(f e d)
    fold proc
        fold proc nil : ideque-front-elements ideq
        reverse : ideque-back-elements ideq

define : ideque-fold-right proc nil ideq
    . "Invokes proc on the elements of ideque in reverse order, passing the result of the previous invocation as a second argument. For the first invocation, nil is used as the second argument. Returns the result of the last invocation, or nil if there was no invocation. Takes O(n) time."
    ##
        tests
            test-equal : fold-right cons '() '(a b c)
                ideque-fold-right cons '() : ideque '(a b c)
            test-equal : fold-right cons '() '(a b c d e f)
                ideque-fold-right cons '() : make-ideque '(a b c) '(f e d)
    fold proc
        fold proc nil : ideque-back-elements ideq
        reverse : ideque-front-elements ideq

define : ideque-append-map proc ideq
    . "Applies proc to the elements of ideque. It is an error if the result is not a list. Returns an ideque containing the elements of the lists in order. Takes O(n) time, where n is the number of elements in all the lists returned."
    ##
        tests
            test-equal '(1 2 3)
                ideque->list
                    ideque-append-map : λ(x) : list x
                        ideque '(1 2 3)
            ;; test-error : ideque-append-map zero? : ideque '(1 2 3)
    ideque-operate-on-elements/internal ideq append-map proc

define : ideque-filter pred ideq
    . "Returns an ideque containing the elements of ideque that do satisfy pred. Takes O(n) time."
    ##
        tests
            test-equal '(2 4 6)
                ideque->list : ideque-filter even? : make-ideque '(1 2 3) '(7 6 5 4)
            test-equal '(1 3)
                ideque->list : ideque-filter odd? : ideque '(1 2 3)
    ideque-operate-on-elements/internal ideq filter pred


define : ideque-remove pred ideq
    . "Returns an ideque containing the elements of ideque that do not satisfy pred. Takes O(n) time."
    ##
        tests
            test-equal '(2 4 6)
                ideque->list : ideque-remove odd? : make-ideque '(1 2 3) '(7 6 5 4)
            test-equal '(1 3)
                ideque->list : ideque-remove even? : ideque '(1 2 3)
    ideque-operate-on-elements/internal ideq remove pred

define : ideque-partition proc ideq
    . "Returns two values, the results of (ideque-filter pred ideque) and (ideque-remove pred ideque) respectively, but may be more efficient. Takes O(n) time."
    ##
        tests
            test-equal '((1 3) (2 4))
                let-values : : (true false) : ideque-partition odd? : ideque '(1 2 3 4)
                    map ideque->list : list true false
    let-values
        : (true-front false-front) : partition proc : ideque-front-elements ideq
          (true-back false-back) : partition proc : ideque-back-elements ideq
        values
            make-balanced-ideque/internal true-front true-back
            make-balanced-ideque/internal false-front false-back

define : ideque-find/internal pred front-elements back-elements . failure
    define found
        or
            find-tail pred front-elements
            find-tail pred : reverse back-elements
    cond
        found
            car found
        : not : null? failure
            : car failure
        else
            . #f

define : ideque-find pred ideq . failure
    . "Returns the first element of ideque that satisfies pred. If there is no such element, returns the result of invoking the thunk failure; the default thunk is (lambda () #f). Takes O(n) time."
    ##
        tests
            test-equal 0
                ideque-find zero? : ideque '(1 2 0 3)
            test-equal 2
                ideque-find even? : ideque '(1 2 0 3)
            test-equal 'failed
                ideque-find even? : ideque '(1 3)
                    λ() 'failed
            test-equal #f
                ideque-find even? : ideque '(1 3)
            test-equal #f
                ideque-find even? : ideque '()
    apply ideque-find/internal pred
        ideque-front-elements ideq
        ideque-back-elements ideq
        . failure

define : ideque-find-right pred ideq . failure
    . "Returns the last element of ideque that satisfies pred. If there is no such element, returns the result of invoking the thunk failure; the default thunk is (lambda () #f). Takes O(n) time."
    ##
        tests
            test-equal 0
                ideque-find-right zero? : ideque '(1 2 0 3)
            test-equal 0
                ideque-find-right even? : ideque '(1 2 0 3)
            test-equal 'failed
                ideque-find-right even? : ideque '(1 3)
                    λ() 'failed
            test-equal #f
                ideque-find-right even? : ideque '(1 3)
            test-equal #f
                ideque-find-right even? : ideque '()
    apply ideque-find/internal pred
        ideque-back-elements ideq
        ideque-front-elements ideq
        . failure

define : ideque-take-while pred ideq
    . "Returns an ideque containing the longest initial prefix of elements in ideque all of which satisfy pred. Takes O(n) time. "
    ##
        tests
            test-equal '(2 4 6)
                ideque->list : ideque-take-while even? : ideque '(2 4 6 1 3 5 8)
    let loop : (res (ideque '())) (ideq ideq)
        if : or (ideque-empty? ideq) : not : pred : ideque-front ideq
            . res
            loop
                ideque-add-back res : ideque-front ideq
                ideque-remove-front ideq


define : ideque-take-while-right pred ideq
    . "Returns an ideque containing the longest final prefix of elements in ideque all of which satisfy pred. Takes O(n) time. "
    ##
        tests
            test-equal '(8)
                ideque->list : ideque-take-while-right even? : ideque '(2 4 6 1 3 5 8)
    let loop : (res (ideque '())) (ideq ideq)
        if : or (ideque-empty? ideq) : not : pred : ideque-back ideq
            . res
            loop
                ideque-add-front res : ideque-back ideq
                ideque-remove-back ideq

define : ideque-drop-while pred ideq
    . "Returns an ideque which omits the longest initial prefix of elements in ideque all of which satisfy pred, but includes all other elements of ideque. Takes O(n) time."
    ##
        tests
            test-equal '(1 3 5 8)
                ideque->list : ideque-drop-while even? : ideque '(2 4 6 1 3 5 8)
    let loop : : ideq ideq
        if : or (ideque-empty? ideq) : not : pred : ideque-front ideq
           . ideq
           loop : ideque-remove-front ideq


define : ideque-drop-while-right pred ideq
    . "Returns an ideque which omits the longest final prefix of elements in ideque all of which satisfy pred, but includes all other elements of ideque. Takes O(n) time."
    ##
        tests
            test-equal '(2 4 6 1 3 5)
                ideque->list : ideque-drop-while-right even? : ideque '(2 4 6 1 3 5 8)
    let loop : : ideq ideq
        if : or (ideque-empty? ideq) : not : pred : ideque-back ideq
           . ideq
           loop : ideque-remove-back ideq

define : ideque-span pred ideq
    . "Returns two values, the initial prefix of the elements of ideque which do satisfy pred, and the remaining elements. Takes O(n) time."
    ##
        tests
            test-equal '((1 3) (6 7 8))
                map ideque->list
                    let-values : : (do do-not) : ideque-span odd? : ideque '(1 3 6 7 8)
                        list do do-not
    let loop : (res (ideque '())) (ideq ideq)
        if : or (ideque-empty? ideq) : not : pred : ideque-front ideq
            values res ideq
            loop
                ideque-add-back res : ideque-front ideq
                ideque-remove-front ideq


define : ideque-break pred ideq
    . "Returns two values, the initial prefix of the elements of ideque which do not satisfy pred, and the remaining elements. Takes O(n) time."
    ##
        tests
            test-equal '((1 3) (6 7 8))
                map ideque->list
                    let-values : : (do do-not) : ideque-break even? : ideque '(1 3 6 7 8)
                        list do do-not
    let loop : (res (ideque '())) (ideq ideq)
        if : or (ideque-empty? ideq) : pred : ideque-front ideq
            values res ideq
            loop
                ideque-add-back res : ideque-front ideq
                ideque-remove-front ideq

define : ideque->generator ideq
    . "Conversion from an ideque to a SRFI 121 generator. Takes O(n) time. A generator is a procedure that is called repeatedly with no arguments to generate consecutive values, and returns an end-of-file object when it has no more values to return. "
    ##
        tests
            test-equal 1
                : ideque->generator : ideque '(1 2 3)
    define gen
        let : : ideq ideq
            lambda :
                if : ideque-empty? ideq
                   eof-object
                   let : : val : ideque-front ideq
                       set! ideq : ideque-remove-front ideq
                       . val
    . gen

define : generator->ideque gen
    . "Conversion from a SRFI 121 generator and an ideque. Takes O(n) time. A generator is a procedure that is called repeatedly with no arguments to generate consecutive values, and returns an end-of-file object when it has no more values to return."
    ##
        tests
            test-equal '(1 2 3)
                ideque->list
                    generator->ideque
                        ideque->generator
                            ideque '(1 2 3)
    let loop : : ideq : ideque '()
        define res : gen
        if : eof-object? res
            . ideq
            loop : ideque-add-back ideq res



;; two further accessors which better match my use-case; these are not in SRFI-134

define : ideque-pop-front ideq
    . "Returns a cons of the ideque with the front element of ideque removed and the retrieved value, similar to assoc. Returns #f for an empty ideque. Takes O(1) time."
    ##
        tests
            test-equal : cons (ideque '()) 1
                ideque-pop-front : make-ideque '(1) '()
            test-equal : cons (ideque '()) 2
                ideque-pop-front
                    car : ideque-pop-front : ideque '(1 2)
            test-equal #f
                ideque-pop-front : ideque '()
    define-values : front back value
        ideque-remove/internal
            ideque-front-elements ideq
            ideque-back-elements ideq
    if front ;; legal ideque
       cons
           make-ideque front back
           . value
       . #f

define : ideque-pop-front! ideq
    . "Returns a cons of the ideque with the front element of ideque removed and the retrieved value, similar to assoc. Returns #f for an empty ideque. Takes O(1) time."
    ##
        tests
            test-equal : cons (ideque '()) 1
                ideque-pop-front : make-ideque '(1) '()
            test-equal : cons (ideque '()) 2
                ideque-pop-front
                    car : ideque-pop-front : make-ideque '(1) '(2)
            test-equal #f
                ideque-pop-front : ideque '()
    define-values : front back value
        ideque-remove/internal
            ideque-front-elements ideq
            ideque-back-elements ideq
    if : not front
       . #f
       begin
           ideque-front-elements-set! ideq front
           ideque-back-elements-set! ideq back
           cons ideq value

define : ideque-pop-back ideq
    . "Returns a cons of the ideque with the front element of ideque removed and the retrieved value, similar to assoc. Returns #f for an empty ideque. Takes O(1) time."
    ##
        tests
            test-equal : cons (ideque '()) 1
                ideque-pop-back : make-ideque '(1) '()
            test-equal : cons (ideque '()) 1
                ideque-pop-back : make-ideque '() '(1)
            test-equal #f
                ideque-pop-back : ideque '()
    define-values : back front value
        ideque-remove/internal
            ideque-back-elements ideq
            ideque-front-elements ideq
    if : not front
       . #f
       cons
           make-ideque front back
           . value

define : ideque-pop-back! ideq
    . "Returns a cons of the ideque with the front element of ideque removed and the retrieved value, similar to assoc. Returns #f for an empty ideque. Takes O(1) time."
    ##
        tests
            test-equal : cons (ideque '()) 1
                ideque-pop-back : make-ideque '(1) '()
            test-equal : cons (ideque '()) 1
                ideque-pop-back : make-ideque '() '(1)
            test-equal #f
                ideque-pop-back : ideque '()
    define-values : back front value
        ideque-remove/internal
            ideque-back-elements ideq
            ideque-front-elements ideq
    if : not front
       . #f
       begin
           ideque-front-elements-set! ideq front
           ideque-back-elements-set! ideq back
           cons ideq value


define %this-module : current-module
define : main args
    when : member "--test" args
        doctests-testmod %this-module
