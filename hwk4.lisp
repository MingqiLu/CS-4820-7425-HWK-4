#|

 Copyright © 2026 by Pete Manolios 
 CS 4820 Fall 2026

 Homework 4.
 Due: 2/16 (Midnight)

 For this assignment, work in groups of 1-2. Send me and the grader
 exactly one solution per team and make sure to follow the submission
 instructions on the course Web page. In particular, make sure that
 the subject of your email submission is "CS 4820 HWK 4".

 The group members are:
 Mingqi Lu (put the names of the group members here)

|#

#|

 In this homework, you will use ACL2s to prove theorems.  Think of
 ACL2s as a proof checker. You give it a proof outline and it checks
 it for you.  The high-level idea is that you provide ACL2s with
 theorems (named properties) that can be proved with, ideally, one
 level of induction. ACL2s will take care of the details, so that you
 do not have to, but you are still responsible for coming up with a
 proof outline.

 To use ACL2s effectively, you need to understand how ACL2s works,
 which we covered in class. For example, recall that theorems can be
 of different types; see rule-classes. Most of your theorems will be
 rewrite rules, so make sure you orient them appropriately and follow
 the other guidelines mentioned in class.  Also, you can specify which
 induction to use or any other hints, using the same options as defthm
 takes (see the documentation).

 The main challenge is figuring out which supporting theorems (lemmas)
 you need to prove the top-level theorems. The use of the professional
 method can be very helpful here. 

 When ACL2s gets stuck or some theorem is not going through, use the
 "method" to figure out what ACL2s does not know that will allow it to
 make progress. 

 For all your proofs in this homework, ACL2s should never do nested
 inductions. If it does, specify an appropriate lemma so that nested
 inductions are not needed.

 This homework has some hard problems, so start early and ask
 questions. 

|#

(in-package "ACL2S")
(set-gag-mode nil) ; ACL2s shows what it is doing.
(set-termination-method :measure)
(set-induction-depth-limit 1)


#|

 Start with the configuration below and once you are done with the
 homework, go to the next configuration, cranking up the rigor all the
 way up to (modeling-admit-all). That is, when you submit your
 homework the form below must be (modeling-admit-all), if you want to
 get full credit.

 After (modeling-start), try (modeling-validate-defs), then 
 (modeling-admit-defs) and finally (modeling-admit-all).

 Tip: once you get one configuration working, you can test that there
 were no errors by going to the shell buffer and typing the following.

 (ubt! 1)
 (ld "hwk4.lisp")

 The first form undoes everything and the second loads hwk4.lisp. For
 the ld to work, you must have started acl2s in the directory where
 hwk4 resides, otherwise you have to specify a path. If the ld
 encounters an error, you will see it and you can see where that error
 occurred by typing

 (pbt 0)

 which will show you what events were accepted.

 Once that is working, change the configuration to the next one and do
 it again, fixing problems until done.

 Each problem has its own configuration, which gives you the
 flexibility work on problems in any order and to have different
 levels of rigor per problem, at a given point in time. All
 configurations should be set to (modeling-admit-all) to get full
 credit.

|#

(modeling-admit-all)

#|

Q1. Consider the following definition

|#

; According to Quan's note on piazza, 
; bad-app is moved below m-bad-app 

#|

 ACL2s accepts the definition, but your job is to come up with a
 measure function and ACL2s proofs of the corresponding proof
 obligations. See the RAP lecture notes on measures; you can use
 generalized measure functions.

|#

; Define, m-bad-app, a measure function for bad-app.
; Q1a. We are using the definition on page 130 of RAP lecture notes

; Note: fill in the ..'s above, as you can use the generalized
; measure functions, as mentioned in Section 5.5.

; Q1b. Fill in the definition

(definec m-bad-app (x y :tl acc :all) :nat
  (if (endp x) (len y)
    (if (endp y) (+ 1 (len x))
      (+ 2 (len x) (len y) (len acc)))))

; The proof obligations for the termination proof of bad-app, using
; properties.  Make sure that ACL2s can prove all of these
; properties. When you increase the configuration for gradual
; verification to the final setting, ACL2s will require proofs. You
; can (and should) prove lemmas as needed. 

; Q1c

(property m-bad-app-x-nil-acc (x acc :tl)
  (implies (consp x)
    (< (m-bad-app nil x acc)
      (m-bad-app x nil acc))))

(property m-bad-app-nil-y-acc (y acc :tl)
  (implies (consp y)
    (< (m-bad-app nil (cdr y) (cons (car y) acc))
      (m-bad-app nil y acc))))

(property m-bad-app-x-y-acc (x y acc :tl temp :all)
  (implies (and (consp x) (consp y))
    (< (m-bad-app x nil temp)
      (m-bad-app x y acc))))

(definec bad-app (x y acc :tl) :tl
  (declare (xargs :measure (m-bad-app x y acc)))
  (match (list x y)
    ((nil nil) acc)
    ((& nil) (bad-app y x acc))
    ((nil (f . r)) (bad-app x r (cons f acc)))
    (& (bad-app x nil (bad-app acc nil y)))))

; Relate bad-app to app.
; Fill in the .. part below. You can only use functions app, rev, if
; and endp. Make sure that ACL2s can prove the property.

; Q1d

(property app-is-append (x y :tl)
  (equal (app x y) (append x y))
  :rule-classes (:rewrite))

(property bad-app-nil-y-acc (x y acc :tl)
  (implies (endp x)
           (== (bad-app x y acc)
               (app (rev y) acc)))
    :hints (("Goal" :induct (bad-app x y acc))))

(property bad-app-x-nil-acc (x y acc :tl)
  (implies (endp y)
           (== (bad-app x y acc)
               (app (rev x) acc)))
    :hints (("Goal" :induct (bad-app x y acc))))

(property (x y :tl)
  (== (bad-app x y nil)
      (if (endp x) (rev y)
        (if (endp y) (rev x)
          (app (rev x) y)))))


; Configuration: update as per instructions

(modeling-admit-all)

#|

Q2. Consider the following definition.

|#

; According to Quan's note on piazza, 
; ack is moved below m-ack 

#|

 ACL2s accepts the definition, but your job is to come up with a
 measure function and ACL2s proofs of the corresponding proof
 obligations. 

|#

; Define, m-ack, a measure function for ack.
; Q2a. We are using the definition on page 132 of RAP lecture notes

; Note: fill in the ..'s above, as you can use the generalized
; measure functions, as mentioned in Section 5.5.

; Q2b. Fill in the definition
(definec m-ack (n :nat m :all) :lex
  (if (natp m) (list n m)
    (list n 0)))

; The proof obligations for the termination proof of ack, using
; properties.  Make sure that ACL2s can prove all of these
; properties. 

; Q2c
(property m-ack-n-0 (n :nat)
  (implies (not (zp n))
    (l< (m-ack (1- n) 1)
      (m-ack n 0))))

(property m-ack-n-m (n m :nat temp :all)
  (implies (not (zp n))
    (l< (m-ack (1- n) temp)
      (m-ack n m))))

(definec ack (n m :nat) :pos
  :skip-tests t ; ack is slow, so skip testing
  (declare (xargs :measure (m-ack n m)))
  (match (list n m)
    ((0 &) (1+ m))
    ((& 0) (ack (1- n) 1))
    (& (ack (1- n) (ack n (1- m))))))


; Configuration: update as per instructions

(modeling-admit-all)

#|

Q3. Consider the following definitions.

|#

(defdata if-atom (or bool var))
(defdata if-expr (or if-atom (list 'if if-expr if-expr if-expr)))
(defdata norm-if-expr (or if-atom (list 'if if-atom norm-if-expr norm-if-expr)))

; Notice that norm-if-expr is a subtype of if-expr.
(defdata-subtype-strict norm-if-expr if-expr)

; The :skip-admissibilityp command below tells ACL2s to skip the
; termination proof, as ACL2s cannot prove termination without help.

; According to Quan's note on piazza, 
; if-flat is moved below m-if-flat

#|

 Since match is a macro, it may help to know exactly what it expands
 into. If you aren't familiar with the backquote/comma duo, look it up
 and it may be useful to see what this expands into also. You can
 check using the ":trans1" form, which expands the top-level form one
 time and expands backquote/commas. To fully expand a form you can use
 ":trans" but that expands lets and conds and so on and may not be
 that readable. Try the following

 :trans1 (match x
           (:if-atom x)
           (('if a b c)
            (match a
              (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
              (('if d e f)
               (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c)))))))

 Notice that the nested match was not expanded, but you can copy that
 form and run trans1 on it to expand it.

|#

; Define, m-if-flat, a measure function for if-flat.
; Q3a. We are using the definition on page 128 of RAP lecture notes


; Q3b. Fill in the definition. This definition must be accepted by
; ACL2s. 
(definec m-if-flat (x :if-expr) :nat
  (match x
    (:if-atom 1)
    (('if a b c) (* (m-if-flat a) (+ (m-if-flat b) (m-if-flat c) 1)))))

; The proof obligations for the termination proof of if-flat, using
; properties.  Make sure that ACL2s can prove all of these
; properties. When you increase the configuration for gradual
; verification to the final setting, ACL2s will require proofs. You
; can (and should) prove lemmas as needed. 

; Q3c

(property m-if-flat->0 (a :if-expr)
  (< 0 (m-if-flat a)))

(property m-if-flat-b<abc (a :if-atom b c :if-expr)
  (< (m-if-flat b)
    (m-if-flat `(if ,a ,b ,c))))

(property m-if-flat-c<abc (a :if-atom b c :if-expr)
  (< (m-if-flat c)
    (m-if-flat `(if ,a ,b ,c))))

(property m-if-flat-debcfeb (d e f b c :if-expr)
  (== (m-if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c)))
      (* (m-if-flat d) (1+ (* (+ (m-if-flat e) (m-if-flat f)) (+ (m-if-flat b) (m-if-flat c) 1))))))

(property m-if-flat-defbc (d e f b c :if-expr)
  (== (m-if-flat `(if (if ,d ,e ,f) ,b ,c))
      (* (m-if-flat d) (+ (m-if-flat e) (m-if-flat f) 1) (+ (m-if-flat b) (m-if-flat c) 1))))

(property m-if-flat-debcfeb<defbc (d e f b c :if-expr)
  (< (m-if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c)))
    (m-if-flat `(if (if ,d ,e ,f) ,b ,c)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable m-if-flat-debcfeb
                              m-if-flat-defbc)
           )))

(definec if-flat (x :if-expr) :norm-if-expr
  (declare (xargs :measure (m-if-flat x)))
  (match x
    (:if-atom x)
    (('if a b c)
     (match a
       (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
       (('if d e f)
        (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c))))))))

#|
 
 We will now prove that if-flat does not change the semantics of if
 expressions using ideas similar to those from HWK2. We will define
 assignments and an evaluator for if expressions.

|#

(defdata if-assign (alistof var bool))

; Notice that if var is not in the if-assign, we return nil.
(definec lookup-var (var :var a :if-assign) :bool
  (match a
    (nil nil)
    (((!var . val) . &) val)
    (& (lookup-var var (cdr a)))))

(definec lookup-atom (e :if-atom a :if-assign) :bool
  (match e
    (:bool e)
    (& (lookup-var e a))))

(definec if-eval (e :if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (if-eval x a) (if-eval y a) (if-eval z a)))))

; Q3d
; State and prove that for all if-assign's, an if-expr e evaluates to
; the same thing as (if-flat e). This should go though automatically,
; but, remember, you have to provide enough lemmas so that there are
; no nested inductions! Also, remember theorems are rewrite rules, so
; orient appropriately.


(property subgoal-not-if-eval (e :if-expr a :if-assign)
  (implies (and (if-exprp e)
                (consp e)
                (equal (car e) 'if)
                (consp (cdr e))
                (consp (cddr e))
                (consp (cdddr e))
                (not (cddddr e))
                (not (booleanp (cadr e)))
                (not (varp (cadr e)))
                (not (consp (cdddr (cadr e))))
                (if-assignp a))
           (not (if-eval e a))))


(property if-flat-equal-if (e :if-expr a :if-assign)
  (== (if-eval (if-flat e) a) 
      (if-eval e a))
  :hints (("Goal" :induct (if-flat e))))


#|

 Check-validp is a simple validity checker for if-expr's.  The idea is
 to use if-flat to normalize the if-expr. Then, we start with an empty
 if-assign and check validity by traversing the expression. When we
 get to a variable that is not assigned, we check that the expression
 is a validity when the variable is t and when it is nil.

|# 

; Lookup assoc-equal in the documentation.
(definec assignedp (e :if-atom a :if-assign) :bool
  (or (boolp e)
      (consp (assoc-equal e a))))

(definec validp (e :norm-if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (assignedp x a)
         (if (lookup-atom x a)
             (validp y a)
           (validp z a))
       (and (validp y (acons x t a))
            (validp z (acons x nil a)))))))

(definec check-validp (e :if-expr) :bool
  (validp (if-flat e) nil))

; Q3e
; 
; Formalize and prove the soundness of check-validp.  That is, if
; (check-validp e) = t, then evaluating e under a, an arbitrary
; if-assign, results in t.

(property validp-is-sound (e :norm-if-expr a b :if-assign)
  :proofs? nil
  (implies (validp e a) 
    (if-eval e (append a b)))
  :hints (("Goal" :induct (validp e a))))

(property check-validp-is-sound (e :if-expr a :if-assign)
  (implies (check-validp e) 
    (if-eval e a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable check-validp)
           :use ((:instance validp-is-sound
                            (e (if-flat e))
                            (a nil)
                            (b a))))))

; Q3f
; 
; Prove that check-validp is complete by showing that when
; check-validp returns nil, there is some if-assign under which the
; if-expr evaluates to nil. With this proof, we now know that
; check-validp is a decision procedure for PL validity.

(definec witness (e :norm-if-expr a :if-assign) :if-assign
  (match e
    (:if-atom a)
    (('if x y z)
     (if (assignedp x a)
         (if (lookup-atom x a)
             (witness y a)
           (witness z a))
       (if (validp y (acons x t a))
           (witness z (acons x nil a))
         (witness y (acons x t a)))))))

(property validp-is-complete (e :norm-if-expr a :if-assign)
  :proofs? nil
  (implies (not (validp e a)) 
    (not (if-eval e (witness e a))))
  :hints (("Goal" :induct (validp e a))))

(property check-validp-is-complete (e :if-expr)
  (implies (not (check-validp e))
           (not (if-eval e (witness (if-flat e) nil))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable check-validp)
           :use ((:instance validp-is-complete
                            (e (if-flat e))
                            (a nil))))))

; Configuration: update as per instructions
(modeling-admit-all)

#|

 Q4. We will now reason about sorting algorithms. Consider the
 following definitions for insert sort and quicksort.

|#

;; See the documentation for <<, which is a total order on the ACL2s
;; universe, so we can compare anything, no matter the types. This
;; allows us to define sorting algorithms that work on integers,
;; rationals, strings, whatever (but using the << ordering).

(definec <<= (x y :all) :bool
  (or (== x y)
      (<< x y)))

(definec insert (a :all x :tl) :tl
  (match x
    (() (list a))
    ((e . es) (if (<<= a e)
                  (cons a x)
                (cons e (insert a es))))))

(definec isort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (insert e (isort es)))))

(definec less (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<< e a)
                  (cons e (less a es))
                (less a es)))))

(definec notless (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<<= a e)
                  (cons e (notless a es))
                (notless a es)))))

(definec qsort (x :tl) :tl
  (match x 
    (() ())
    ((e . es) (append (qsort (less e es))
                   (list e)
                   (qsort (notless e es))))))

#|

 Q4. Prove the following property.

 This is not easy, so I strongly recommend that you come up with a
 plan and use the professional method to sketch out a proof.

|#

(definec ordered (x :tl) :bool
  (or (endp x)
      (endp (cdr x))
      (and (<<= (car x) (cadr x))
           (ordered (cdr x)))))

(property insert-ordered (x :tl a :all)
  (implies (ordered x)
          (ordered (insert a x))))

(property isort-ordered (x :tl)
  (ordered (isort x))
  :hints (("Goal" :induct (isort x))))

(property less-insert-a<<=b (x :tl a b :all)
  (implies (<<= a b)
          (== (less a (insert b x))
              (less a x))))

(property less-insert-b<<a (x :tl a b :all)
  :proofs? nil
  (implies (and (ordered x) (<< b a))
           (== (insert b (less a x))
               (less a (insert b x)))))

(property swap-isort-less (x :tl a :all)
  (== (isort (less a x))
      (less a (isort x))))

(property notless-insert-b<<a (x :tl a b :all)
  (implies (<< b a)
          (== (notless a (insert b x))
              (notless a x))))

(property notless-insert-a<<=b (x :tl a b :all)
  :proofs? nil
  (implies (and (ordered x) (<<= a b))
          (== (insert b (notless a x))
              (notless a (insert b x)))))

(property swap-isort-notless (x :tl a :all)
  (== (isort (notless a x))
      (notless a (isort x))))

(property insert-least-less (x :tl a :all)
  (implies (and (ordered x) (<<= a (car x)))
          (== (less a x) nil)))

(property insert-least-notless (x :tl a :all)
  (implies (and (ordered x) (<<= a (car x)))
          (== (notless a x) x)))

(property split-isort (x :tl a :all)
  (implies (ordered x)
    (== (insert a x)
        (append (less a x) (cons a (notless a x))))))

(property qsort=isort (x :tl)
  (== (qsort x)
      (isort x)))

#|
 Extra Credit 1. (25 points each, all or nothing)


 1. First, prove (in ACL2s) that if x and y are ordered true lists,
 under <<=, and permutations of each other, they are equal. Second,
 prove that qsort and isort return ordered permutations of their
 input.
|#

(definec perm (x y :tl) :bool
  (== (isort x)
      (isort y)))

(property ordered-isort-equal (x :tl)
  (implies (ordered x)
          (== (isort x) x))
  :hints (("Goal"
         :in-theory (disable split-isort))))

(property ordered-permp-equal (x y :tl)
  (implies (and (ordered x) (ordered y) (perm x y))
          (== x y))
  :rule-classes nil)

(property ordered-permutation-isort (x :tl)
  (and (ordered (isort x))
      (perm x (isort x))))

(property ordered-permutation-qsort (x :tl)
  (and (ordered (qsort x))
      (perm x (qsort x))))

#|
 2. Do the homework in another theorem prover of your choice. Try to
 make it as equivalent as possible. Provide a summary of your
 findings.  This is only recommended for those of you that already
 have experience with other theorem provers. ACL2 is not allowed this
 time.

|#