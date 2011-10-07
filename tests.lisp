(in-package "ACL2")
(program)
(include-book "proof-checker")
(include-book "my-cw")

; Print everything to console
(defmacro output-file ()
  nil)

;;;;;;;;;;;;;;;;;;;
;;; GOOD PROOFS ;;;
;;;;;;;;;;;;;;;;;;;

; BASIC TESTS

; Problem: given a = b and b = c, prove g(f(a), b) = g(f(c), a)
(defun rules1 ()
  '((=refl (= x x))
    (=symm (implies (= x y) (= y x)))
    (=trans (implies (and (= x y) (= y z)) (= x z)))
    (fcong (implies (= x y) (= (f x) (f y))))
    (gcong (implies (and (= x y) (= z w)) (= (g x z) (g y w))))))
(defun assumptions1 ()
  '((assumption1 (= a b))
    (assumption2 (= b c))))
(defun proof1 ()
  '((step1 (= a c) =trans ((x a) (y b) (z c)) (assumption1 assumption2))
    (step2 (= (f a) (f c)) fcong ((x a) (y c)) (step1))
    (step3 (= b a) =symm ((x a) (y b)) (assumption1))
    (step4 (= (g (f a) b) (g (f c) a)) gcong ((x (f a)) (z b) (y (f c)) (w a)) (step2 step3))))
(defun prove1 ()
  (prog2$
    (my-cw (output-file) "Running prove1...~%")
    (proof-check (output-file) (assumptions1) (rules1) (proof1) nil '(r s a) 0)))

(defun prove1-goal ()
  (prog2$
    (my-cw (output-file) "Running prove1-goal...~%")
    (verify-proof (output-file) '(= (g (f a) b) (g (f c) a)) (assumptions1) (rules1) (proof1) nil '(r s a) 0)))

; Note that this proves 3 intermediate statements with depth 2, since they are not nested in series
(defun proof1-auto ()
  '((step4 (= (g (f a) b) (g (f c) a)) nil nil nil)))
(defun prove1-auto ()
  (prog2$
    (my-cw (output-file) "Running prove1-auto...~%")
    (proof-check (output-file) (assumptions1) (rules1) (proof1-auto) nil nil 2)))

; Problem: Prove a * (b - b) = 0
; TODO Think about a more natural way to do substitutions?
(defun rules2 ()
  '((times0 (implies (= y 0) (= (* x y) 0)))
    (sub-self (implies (= x y) (= (- x y) 0)))
    (=symm (implies (= x y) (= y x)))
    (=refl (= x x))))
(defun proof2 ()
  '((step1 (= b b) nil nil nil)
    (step2 (= (- b b) 0) nil nil nil)
    (step3 (= (* a (- b b)) 0) nil nil nil)))
(defun prove2 ()
  (prog2$
    (my-cw (output-file) "Running prove2...~%")
    (proof-check (output-file) nil (rules2) (proof2) nil nil 0)))

(defun proof2-auto ()
  '((step3 (= (* a (- b b)) 0) nil nil nil)))
(defun prove2-auto ()
  (prog2$
    (my-cw (output-file) "Running prove2-auto...~%")
    (proof-check (output-file) nil (rules2) (proof2-auto) nil nil 2)))

; Tests proofs with no assumptions
(defun rules3 ()
  '((rule1 (= (f) (g)))))
(defun proof3 ()
  '((step1 (= (f) (g)) nil nil nil)))
(defun prove3 ()
  (prog2$
    (my-cw (output-file) "Running prove3...~%")
    (proof-check (output-file) nil (rules3) (proof3) nil nil 0)))

; Tests that only variables are substituted, not function names
(defun rules4 ()
  '((test (a a a))))
(defun proof4 ()
  '((step1 (a b b) test nil nil)))
(defun prove4 ()
  (prog2$
    (my-cw (output-file) "Running prove4...~%")
    (proof-check (output-file) nil (rules4) (proof4) nil nil 0)))

; GRAMMAR TESTS

; Basic grammar: balanced brackets (OLD format)
(defun assumptions5 ()
  '((base (isBal))))
(defun rules5 ()
  '((surround (implies (isBal x) (isBal [ x ])) (x y))
    (append (implies (and (isBal x) (isBal y)) (isBal x y)) (x y))))
(defun proof5 ()
  '((step1 (isBal [ ]) nil nil nil)
    (step2 (isBal [ ] [ ]) nil nil nil)
    (step3 (isBal [ [ ] [ ] ]) nil nil nil)
    (step4 (isBal [ [ [ ] [ ] ] ]) nil nil nil)))
(defun prove5 ()
  (prog2$
    (my-cw (output-file) "Running prove5...~%")
    (proof-check (output-file) (assumptions5) (rules5) (proof5) '([ ]) nil 0)))

; Balanced brackets (CURRENT format)
(defun assumptions5b ()
  '((base (-*> B B))
    (eps (-> B))
    (surround (-> B [ B ]))
    (append (-> B B B))))
(defun rules5b ()
  ; Note: nonterm is constrained to refer to exactly one term
  '((prod (implies (and (-*> nonterm s1 B s2) (-> B rep)) (-*> nonterm s1 rep s2)) (s1 rep s2))))
(defun proof5b ()
  '((1 (-*> B [ B ]) prod nil (base surround))
    (2 (-*> B [ [ B ] ]) nil nil nil)
    (3 (-*> B [ [ B B ] ]) nil nil nil)
    (4 (-*> B [ [ [ B ] B ] ]) nil nil nil)
    (5 (-*> B [ [ [ B ] [ B ] ] ]) nil nil nil)
    (6 (-*> B [ [ [ ] [ B ] ] ]) nil nil nil)
    (7 (-*> B [ [ [ ] [ ] ] ]) nil nil nil)))
(defun prove5b ()
  (prog2$
    (my-cw (output-file) "Running prove5b...~%")
    (proof-check (output-file) (assumptions5b) (rules5b) (proof5b) '(B [ ]) nil 0)))

(defun proof5b-auto ()
   '((4 (-*> B [ [ [ B ] B ] ]) nil nil nil)
     (7 (-*> B [ [ [ ] [ ] ] ]) nil nil nil)))
(defun prove5b-auto ()
  (prog2$
    (my-cw (output-file) "Running prove5b-auto... (should be a few seconds)~%")
    (proof-check (output-file) (assumptions5b) (rules5b) (proof5b-auto) '(B [ ]) nil 3)))

; TODO This test is disabled because it uses recursion depth 6, which is currently too much for the
;      proof-checker to handle!
(defun proof5b-auto-full ()
  '((7 (-*> B [ [ [ ] [ ] ] ]) nil nil nil)))
(defun prove5b-auto-full ()
  (prog2$
    (my-cw (output-file) "Running prove5b-auto-full...~%")
    (proof-check (output-file) (assumptions5b) (rules5b) (proof5b-auto) '(B [ ]) nil 6)))

; Simple CFG (old format) - example from CS 143 WA2, #2
(defun rules6 ()
  '((s1 (implies (and (isT t1) (isU u1)) (isS x t1 u1)) (t1 u1))
    (s2 (implies (isX x1) (isS l x1)) (x1))
    (s3 (implies (isX x1) (isS x1)) (x1))
    (t1 (isT c))
    (t2 (isT l))
    (x1 (implies (isX x1) (isX x x1)) (x1))
    (x2 (implies (isU u1) (isX u1)) (u1))
    (u1 (implies (isY y1) (isU i y1)) (y1))
    (u2 (implies (isI i1) (isU v i1)) (i1))
    (u3 (implies (isI i1) (isU i1)) (i1))
    (y1 (isY x))
    (y2 (isY v))
    (i1 (implies (isI i1) (isI i i1)) (i1))
    (i2 (isI))))
(defun proof6 ()
  '((step1 (isT l) nil nil nil)
    (step2 (isI) nil nil nil)
    (step3 (isI i) nil nil nil)
    (step4 (isI i i) nil nil nil)
    (step5 (isU v i i) nil nil nil)
    (step6 (isS x l v i i) nil nil nil)))
(defun prove6 ()
  (prog2$
    (my-cw (output-file) "Running prove6...~%")
    (proof-check (output-file) nil (rules6) (proof6) '(c l x v i) nil 0)))

; Simple CFG (current format) - example from CS 143 WA2, #2
(defun assumptions6b ()
  '((baseS (-*> S S))
    (s1 (-> S _x T U))
    (s2 (-> S _l X))
    (s3 (-> S X))
    (t1 (-> T _c))
    (t2 (-> T _l))
    (x1 (-> X _x X))
    (x2 (-> X _x U))
    (u1 (-> U _i Y))
    (u2 (-> U _v I))
    (u3 (-> U I))
    (y1 (-> Y _x))
    (y2 (-> Y _v))
    (i1 (-> I _i I))
    (i2 (-> I))))
(defun rules6b ()
  '((prod (implies (and (-*> nonterm s1 lhs s2) (-> lhs rep)) (-*> nonterm s1 rep s2)) (s1 rep s2))))
(defun proof6b ()
  '((1 (-*> S _x T U) nil nil nil)
    (2 (-*> S _x _l U) nil nil nil)
    (3 (-*> S _x _l _v I) nil nil nil)
    (4 (-*> S _x _l _v _i I) nil nil nil)
    (5 (-*> S _x _l _v _i _i I) nil nil nil)
    (6 (-*> S _x _l _v _i _i) nil nil nil)))
(defun prove6b ()
  (prog2$
    (my-cw (output-file) "Running prove6b...~%")
    (proof-check (output-file) (assumptions6b) (rules6b) (proof6b) '(S T X U Y I _x _l _c _v _i) nil 0)))

(defun rules6b-auto ()
  '((prodS (implies (and (-*> nonterm s1 S s2) (-> S rep)) (-*> nonterm s1 rep s2)) (s1 rep s2))
    (prodT (implies (and (-*> nonterm s1 T s2) (-> T rep)) (-*> nonterm s1 rep s2)) (s1 rep s2))
    (prodX (implies (and (-*> nonterm s1 X s2) (-> X rep)) (-*> nonterm s1 rep s2)) (s1 rep s2))
    (prodU (implies (and (-*> nonterm s1 U s2) (-> U rep)) (-*> nonterm s1 rep s2)) (s1 rep s2))
    (prodY (implies (and (-*> nonterm s1 Y s2) (-> Y rep)) (-*> nonterm s1 rep s2)) (s1 rep s2))
    (prodI (implies (and (-*> nonterm s1 I s2) (-> I rep)) (-*> nonterm s1 rep s2)) (s1 rep s2))))
(defun proof6b-auto ()
  '((4 (-*> S _x _l _v _i I) nil nil nil)
    (6 (-*> S _x _l _v _i _i) nil nil nil)))
(defun prove6b-auto ()
  (prog2$
    (my-cw (output-file) "Running prove6b-auto... (should be about half a minute) ~%")
    (proof-check (output-file) (assumptions6b) (rules6b-auto) (proof6b-auto) '(S T X U Y I _x _l _c _v _i) nil 3)))

; TODO This test is disabled because it uses recursion depth 5, which is currently too much for the
;      proof-checker to handle!
(defun proof6b-auto-full ()
  '((6 (-*> S _x _l _v _i _i) nil nil nil)))
(defun prove6b-auto-full ()
  (prog2$
    (my-cw (output-file) "Running prove6b-auto-full...~%")
    (proof-check (output-file) (assumptions6b) (rules6b-auto) (proof6b-auto-full) '(S T X U Y I _x _l _c _v _i) nil 5)))

; Context-sensitive grammars (current format) - first example from Wikipedia
(defun assumptions7 ()
  '((baseS (-*> S S))
    (prod1 (-> S - _a S B C))
    (prod2 (-> S - _a B C))
    (prod3 (-> C B - H B))
    (prod4 (-> H B - H C))
    (prod5 (-> H C - B C))
    (prod6 (-> _a B - _a _b))
    (prod7 (-> _b B - _b _b))
    (prod8 (-> _b C - _b _c))
    (prod9 (-> _c C - _c _c))))
(defun rules7 ()
  '((prod (implies (and (-*> nonterm s1 lhs s2) (-> lhs - rep)) (-*> nonterm s1 rep s2)) (s1 lhs rep s2))))
(defun proof7 ()
  '((01 (-*> S _a S B C) nil nil nil)
    (02 (-*> S _a _a S B C B C) nil nil nil)
    (03 (-*> S _a _a _a B C B C B C) nil nil nil)
    (04 (-*> S _a _a _a B H B C B C) nil nil nil)
    (05 (-*> S _a _a _a B H C C B C) nil nil nil)
    (06 (-*> S _a _a _a B B C C B C) nil nil nil)
    (07 (-*> S _a _a _a B B C H B C) nil nil nil)
    (08 (-*> S _a _a _a B B C H C C) nil nil nil)
    (09 (-*> S _a _a _a B B C B C C) nil nil nil)
    (10 (-*> S _a _a _a B B H B C C) nil nil nil)
    (11 (-*> S _a _a _a B B H C C C) nil nil nil)
    (12 (-*> S _a _a _a B B B C C C) nil nil nil)
    (13 (-*> S _a _a _a _b B B C C C) nil nil nil)
    (14 (-*> S _a _a _a _b _b B C C C) nil nil nil)
    (15 (-*> S _a _a _a _b _b _b C C C) nil nil nil)
    (16 (-*> S _a _a _a _b _b _b _c C C) nil nil nil)
    (17 (-*> S _a _a _a _b _b _b _c _c C) nil nil nil)
    (18 (-*> S _a _a _a _b _b _b _c _c _c) nil nil nil)))
(defun prove7 ()
  (prog2$
    (my-cw (output-file) "Running prove7...~%")
    (proof-check (output-file) (assumptions7) (rules7) (proof7) '(S B C H _a _b _c -) nil 0)))

; Context-sensitive grammars (current format) - second example from Wikipedia
(defun assumptions8 ()
  '((baseS (-*> S S))
    (s1 (-> S - _a A S))
    (s2 (-> S - _b B S))
    (s3 (-> S - T))
    (aa (-> A _a - _a A))
    (ba (-> B _a - _a B))
    (ab (-> A _b - _b A))
    (bb (-> B _b - _b B))
    (bt (-> B T - T _b))
    (at (-> A T - T _a))
    (t_ (-> T -))))
(defun rules8 ()
  '((prod (implies (and (-*> nonterm s1 lhs s2) (-> lhs - rep)) (-*> nonterm s1 rep s2)) (s1 lhs rep s2))))
(defun proof8 ()
  '((1 (-*> S _a A S) nil nil nil)
    (2 (-*> S _a A _b B S) nil nil nil)
    (3 (-*> S _a A _b B T) nil nil nil)
    (4 (-*> S _a _b A B T) nil nil nil)
    (5 (-*> S _a _b A T _b) nil nil nil)
    (6 (-*> S _a _b T _a _b) nil nil nil)
    (7 (-*> S _a _b _a _b) nil nil nil)))
(defun prove8 ()
  (prog2$
    (my-cw (output-file) "Running prove8...~%")
    (proof-check (output-file) (assumptions8) (rules8) (proof8) '(S A B T _a _b -) nil 0)))

; Tests that substitutions obey format restrictions
(defun rules9 ()
  '((num (= (* a 0) 0) nil ((a number)))
    (str (isString b) nil ((b string)))))
(defun proof9 ()
  '((1 (= (* 5 0) 0) nil nil nil)
    (2 (isString "abc") nil nil nil)))
(defun prove9 ()
  (prog2$
    (my-cw (output-file) "Running prove9...~%")
    (proof-check (output-file) nil (rules9) (proof9) nil nil 0)))

; COOL - Prove some things about the types of various expressions
; TODO Allow for SELF_TYPE, test more thoroughly (negative tests!)
; TODO Environment checking isn't completely rigorous... You can prove (isValidEnv (env (obj a String) (obj a Int)))
(defun assumptions10 ()
  '((validenv-base (isValidEnv (env)))
    (c1 (class Object))
    (c1m1 (method Object abort Object))
    (c1m2 (method Object type_name String))
;   (c1m3 (method Object copy SELF_TYPE))
    (c2 (class IO))
;   (c2m1 (method IO out_string String SELF_TYPE))
;   (c2m2 (method IO out_int Int SELF_TYPE))
    (c2m3 (method IO in_string String))
    (c2m4 (method IO in_int Int))
    (c3 (class Int))
    (c4 (class Bool))
    (c5 (class String))
    (c5m1 (method String length Int))
    (c5m2 (method String concat String String))
    (c5m3 (method String substr Int Int String))
    (sub21 (<= IO Object))
    (sub31 (<= Int Object))
    (sub41 (<= Bool Object))
    (sub51 (<= String Object))
    (lub12 (lub Object Object IO))
    (lub13 (lub Object Object Int))
    (lub14 (lub Object Object Bool))
    (lub15 (lub Object Object String))
    (lub23 (lub Object IO Int))
    (lub24 (lub Object IO Bool))
    (lub25 (lub Object IO String))
    (lub34 (lub Object Int Bool))
    (lub35 (lub Object Int String))
    (lub36 (lub Object Bool String))))
(defun rules10 ()
  '((validenv-build (implies (and (isValidEnv (env orig)) (class type)) (isValidEnv (env orig (obj id type)))) (orig))
    (symmlub (implies (and (class x) (class y) (class z) (lub x y z)) (lub x z y)))
    (selflub (implies (class x) (lub x x x)))
    (selfeql (implies (class x) (= x x)))
    (subtrans (implies (and (class a) (class b) (class c) (<= a b) (<= b c)) (<= a c)))
    (selfsub (implies (class x) (<= x x)))
    ; ... rules about actual expression constructs
    (var (implies (and (class T) (isValidEnv (env s1 (obj id T) s2))) (turns (env s1 (obj id T) s2) id hasType T)) (s1 s2))
    (assign (implies (and (isValidEnv (env s1 (obj id T) s2)) (turns (env s1 (obj id T) s2) e1 hasType T1) (class T) (class T1) (<= T1 T)) (turns (env s1 (obj id T) s2) id <- e1 hasType T1)) (s1 s2 e1))
    (true (implies (isValidEnv O) (turns O true hasType Bool)))
    (false (implies (isValidEnv O) (turns O false hasType Bool)))
    (int (implies (isValidEnv O) (turns O i hasType Int)) nil ((i number)))
    (string (implies (isValidEnv O) (turns O s hasType String)) nil ((s string)))
    (new (implies (and (isClass T) (isValidEnv O)) (turns O new T hasType T)))
    (dispatch2 (implies (and (isValidEnv O) (turns O e0 hasType T0) (turns O e1 hasType T1) (turns O e2 hasType T2) (turns O e3 hasType T3) (method T0 f T1p T2p T3p) (<= T1 T1p) (<= T2 T2p) (<= T3 T3p) (= T3 T3p)) (turns O e0 dot f op e1 comma e2 cp hasType T3)) (e0 e1 e2 e3))
    (if (implies (and (isValidEnv O) (turns O e1 hasType Bool) (turns O e2 hasType T2) (turns O e3 hasType T3) (lub T T2 T3)) (turns O if e1 then e2 else e3 fi hasType T)) (e1 e2 e3))
    (let-init (implies (and (isValidEnv (env s)) (= T0p T0) (turns (env s) e1 hasType T1) (<= T1 T0p) (turns (env s (obj x T0p)) e2 hasType T2)) (turns (env s) let x colon T0 <- e1 in e2 hasType T2)) (s e1 e2))
    (plus (implies (and (isValidEnv O) (turns O e1 hasType Int) (turns O e2 hasType Int)) (turns O e1 + e2 hasType Int)))))
(defun proof10 ()
  '((pre1 (= String String) nil nil nil)
    (pre2 (<= String String) nil nil nil)
    (pre3 (lub Object String Int) nil nil nil)
    (env1 (isValidEnv (env (obj y Int))) nil nil nil)
    (env2 (isValidEnv (env (obj y Int) (obj x String))) nil nil nil)
    (1 (turns (env (obj y Int)) "blah" hasType String) nil nil nil)
    (2 (turns (env (obj y Int) (obj x String)) true hasType Bool) nil nil nil)
    (3 (turns (env (obj y Int) (obj x String)) x hasType String) var nil nil)
    (4 (turns (env (obj y Int) (obj x String)) 4 hasType Int) nil nil nil)
    (5 (turns (env (obj y Int) (obj x String)) y hasType Int) nil nil nil)
    (6 (turns (env (obj y Int) (obj x String)) 4 + y hasType Int) nil nil nil)
    (7 (turns (env (obj y Int) (obj x String)) if true then x else 4 + y fi hasType Object) nil nil nil)
    (8 (turns (env (obj y Int)) let x colon String <- "blah" in if true then x else 4 + y fi hasType Object) nil nil nil)))
(defun prove10 ()
  (prog2$
    (my-cw (output-file) "Running prove10...~%")
    (proof-check (output-file) (assumptions10) (rules10) (proof10) '(Object abort type_name IO in_string in_int Int Bool String length concat substr true false <- colon comma dot op cp hasType if then else fi let in +) nil 0)))

; Tests that the proof-checker can correctly unify ((a b) a) with ((x y) x), where both a and b are
; strings. This means that the proof-checker will use the wrong substitutions when unifying (a b)
; and (x y), fail, and backtrack properly.
(defun rules11 ()
  '((rule (list (list a b) a) (a b))))
(defun proof11 ()
  '((1 (list (list x y) x) nil nil nil)))
(defun prove11 ()
  (prog2$
    (my-cw (output-file) "Running prove11...~%")
    (proof-check (output-file) nil (rules11) (proof11) nil nil 0)))

; Ensures that backtracking will work during assumptions as well. The proof-checker should unify
; (a) with (x), then use the substitutions ((b) (c y z)) when unifying with a1. This will fail
; during attempts to unify a1 and a2 with (b a c). Then, the proof-checker must backtrack, using
; the substitutions ((b y) (c z)) instead, and successfully prove the conclusion.
(defun rules12 ()
  '((rule (implies (and (list b c) (list b a c)) (list a)) (a b c))))
(defun assumptions12 ()
  '((a1 (list y z))
    (a2 (list y x z))))
(defun proof12 ()
  '((1 (list x) nil nil nil)))
(defun prove12 ()
  (prog2$
    (my-cw (output-file) "Running prove12...~%")
    (proof-check (output-file) (assumptions12) (rules12) (proof12) nil nil 0)))

; Basic proof
(defun rules13 ()
  '((=symm (implies (= x y) (= y x)))
    (fcong (implies (= x y) (= (f x) (f y))))))
(defun assumptions13 ()
  '((a1 (= a b))))
(defun proof13 ()
  '((1 (= b a) nil nil nil)
    (2 (= (f b) (f a)) nil nil nil)))
(defun prove13 ()
  (prog2$
    (my-cw (output-file) "Running prove13...~%")
    (proof-check (output-file) (assumptions13) (rules13) (proof13) nil nil 0)))

; Same as basic proof, but now using search to avoid stating step 1
(defun proof13-auto ()
  '((1 (= (f b) (f a)) nil nil nil)))
(defun prove13-auto ()
  (prog2$
    (my-cw (output-file) "Running prove13-auto...~%")
    (proof-check (output-file) (assumptions13) (rules13) (proof13-auto) nil nil 1)))

; Actually going to depth 100000 would be bad, solution should be found before that
(defun prove13-auto2 ()
  (prog2$
    (my-cw (output-file) "Running prove13-auto2...~%")
    (proof-check (output-file) (assumptions13) (rules13) (proof13-auto) nil nil 100000)))

(defun rules14 ()
  '((=refl (= x x))
    (=rep (implies (= y z) (= (+ x y) (+ x z))))
    (+comm (implies (= x (+ y z)) (= x (+ z y))))
    (=symm (implies (= y z) (= z y)))
    (=trans (implies (and (= x y) (= y z)) (= x z)))))
(defun assumptions14 ()
  '((1+2 (= (+ 1 2) 3))
    (3+3 (= (+ 3 3) 6))))
(defun proof14 ()
  '((1 (= (+ 1 2) (+ 1 2)) =refl nil nil)
    (2 (= (+ (+ 1 2) (+ 1 2)) (+ (+ 1 2) 3)) =rep nil nil)
    (3 (= (+ (+ 1 2) (+ 1 2)) (+ 3 (+ 1 2))) +comm nil nil)
    (4 (= (+ 3 (+ 1 2)) (+ 3 3)) =rep nil nil)
    (5 (= (+ 3 (+ 1 2)) 6) =trans nil nil)
    (6 (= (+ (+ 1 2) (+ 1 2)) 6) =trans nil nil)))
(defun prove14 ()
  (prog2$
    (my-cw (output-file) "Running prove14...~%")
    (proof-check (output-file) (assumptions14) (rules14) (proof14) nil nil 0)))

(defun proof14-auto ()
  '((2b (= (+ (+ 1 2) (+ 1 2)) (+ 3 (+ 1 2))) nil nil nil)
    (2c (= (+ 3 (+ 1 2)) (+ 3 3)) nil nil nil)
    (3 (= (+ (+ 1 2) (+ 1 2)) (+ 3 3)) nil nil nil)
    (4 (= (+ (+ 1 2) (+ 1 2)) 6) nil nil nil)))
(defun prove14-auto ()
  (prog2$
    (my-cw (output-file) "Running prove14-auto...~%")
    (proof-check (output-file) (assumptions14) (rules14) (proof14-auto) nil nil 1)))

(defun proof15-auto ()
  '((1 (= (+ (+ 1 2) (+ 3 (+ 1 2))) (+ (+ 1 2) (+ 3 3))) nil nil nil)))
(defun prove15-auto ()
  (prog2$
    (my-cw (output-file) "Running prove15-auto...~%")
    (proof-check (output-file) (assumptions14) (rules14) (proof15-auto) nil nil 1)))

;;;;;;;;;;;;;;;;;;
;;; BAD PROOFS ;;;
;;;;;;;;;;;;;;;;;;

(defun badalistp ()
  '((step1 (= b b) =refl (x b) nil)))
(defun badalist-prove ()
  (prog2$
    (my-cw (output-file) "Running badalist-prove: should fail with bad association list.~%")
    (proof-check (output-file) nil (rules2) (badalistp) nil nil 0)))

(defun badalist2p ()
  '((step1 (= b b) =refl (((x b) c)) nil)))
(defun badalist2-prove ()
  (prog2$
    (my-cw (output-file) "Running badalist2-prove: should fail with non-atom mapping.~%")
    (proof-check (output-file) nil (rules2) (badalist2p) nil nil 0)))

(defun dupnamesa ()
  '((assump (equiv a b))
    (assump (equiv b c))))
(defun dupnamesp ()
  '((step1 (equiv x y) assump ((a x) (b y)) nil)))
(defun dupnames-prove ()
  (prog2$
    (my-cw (output-file) "Running dupnames-prove: should fail with duplicate names.~%")
    (proof-check (output-file) (dupnamesa) nil (dupnamesp) nil nil 0)))

; TODO Needs consistency - this will succeed if the substitution is allowed
(defun forbiddensubr ()
  '((=refl (= + +))))
(defun forbiddensubp ()
  '((1 (= x x) =refl ((+ x)) nil)))
(defun forbiddensub-prove ()
  (prog2$
    (my-cw (output-file) "Running forbiddensub-prove: should fail with forbidden name +.~%")
    (proof-check (output-file) nil (forbiddensubr) (forbiddensubp) nil nil 0)))

(defun nummapp ()
  '((pf (= b b) =refl ((1 b)) nil)))
(defun nummap-prove ()
  (prog2$
    (my-cw (output-file) "Running nummap-prove: should fail with mapping to number.~%")
    (proof-check (output-file) nil (rules2) (nummapp) nil nil 0)))

(defun badruleslen1r ()
  '((blah)))
(defun badruleslen1-prove ()
  (prog2$
    (my-cw (output-file) "Running badruleslen1r-prove: should fail with bad length.~%")
    (proof-check (output-file) nil (badruleslen1r) nil nil nil 0)))

(defun badruleslen2r ()
  '((blah (= x x) nil nil nil)))
(defun badruleslen2-prove ()
  (prog2$
    (my-cw (output-file) "Running badruleslen2r-prove: should fail with bad length.~%")
    (proof-check (output-file) nil (badruleslen2r) nil nil nil 0)))

(defun badassumplena ()
  '((assump = a b)))
(defun badassumplena-prove ()
  (prog2$
    (my-cw (output-file) "Running badassumplena-prove: should fail with bad length.~%")
    (proof-check (output-file) (badassumplena) (rules2) (proof2) nil nil 0)))

(defun badassumpstmta ()
  '((assump ((= a b)))))
(defun badassumpstmt-prove ()
  (prog2$
    (my-cw (output-file) "Running badassumpstmt-prove: should fail with malformed expression.~%")
    (proof-check (output-file) (badassumpstmta) (rules2) (proof2) nil nil 0)))

(defun defconstr ()
  '((withconst (= x x))))
(defun defconstp ()
  '((step1 (= y y) withconst ((x y)) nil)))
(defun defconst-prove ()
  (prog2$
    (my-cw (output-file) "Running defconst-prove: should fail with forbidden name error.~%")
    (proof-check (output-file) nil (defconstr) (defconstp) '(x) nil 0)))

(defun atomkeyr ()
  '(((rule name) (= x x))))
(defun atomkeyp ()
  '((1 (= y y) (rule name) ((x y)) nil)))
(defun atomkey-prove ()
  (prog2$
    (my-cw (output-file) "Running atomkey-prove: should fail with non-atom key errors in both rule and proof.~%")
    (proof-check (output-file) nil (atomkeyr) (atomkeyp) nil nil 0)))

(defun missingassumpp ()
  '((1 (= a b) =symm nil nil)))
(defun missingassump-prove ()
  (prog2$
    (my-cw (output-file) "Running missingassump-prove: should fail to prove step 1.~%")
    (proof-check (output-file) nil (rules1) (missingassumpp) nil nil 0)))

(defun badstrvarsr ()
  '((badrule (= x 0) (0))))
(defun badstrvars-prove ()
  (prog2$
    (my-cw (output-file) "Running badstrvars-prove: should say str-vars contains constants.~%")
    (proof-check (output-file) nil (badstrvarsr) nil nil nil 0)))

(defun badstrvars2r ()
  '((badrule (= x 0) (a (b c)))))
(defun badstrvars2-prove ()
  (prog2$
    (my-cw (output-file) "Running badstrvars2-prove: should say str-vars contains constants.~%")
    (proof-check (output-file) nil (badstrvars2r) nil nil nil 0)))

(defun nomatchp ()
  '((1 (-*> B [ x_b) prod nil nil)))
(defun nomatch-prove ()
  (prog2$
    (my-cw (output-file) "Running nomatch-prove: should fail to prove step 1.~%")
    (proof-check (output-file) (assumptions5b) (rules5b) (nomatchp) '(B [ ] x_b) nil 0)))

(defun nomatch2p ()
  '((1 (-*> B [ x_b ] ]) prod nil nil)))
(defun nomatch2-prove ()
  (prog2$
    (my-cw (output-file) "Running nomatch2-prove: should fail to prove step 1.~%")
    (proof-check (output-file) (assumptions5b) (rules5b) (nomatch2p) '(B [ ] x_b) nil 0)))

(defun nomatch3p ()
  '((1 (-*> B [ x_b x_b ]) prod nil nil)))
(defun nomatch3-prove ()
  (prog2$
    (my-cw (output-file) "Running nomatch3-prove: should fail to prove step 1.~%")
    (proof-check (output-file) (assumptions5b) (rules5b) (nomatch3p) '(B [ ] x_b) nil 0)))

(defun badsublenr ()
  '((rule (f x))))
(defun badsublenp ()
  '((1 (f) rule ((x)) nil)))
(defun badsublen-prove ()
  (prog2$
    (my-cw (output-file) "Running badsublen-prove: should report bad substitution.~%")
    (proof-check (output-file) nil (badsublenr) (badsublenp) nil nil 0)))

(defun badsublen2p ()
  '((1 (f a b) rule ((x a b)) nil)))
(defun badsublen2-prove ()
  (prog2$
    (my-cw (output-file) "Running badsublen2-prove: should report bad substitution.~%")
    (proof-check (output-file) nil (badsublenr) (badsublen2p) nil nil 0)))

(defun badmatchlenp ()
  '((1 (f) rule nil nil)))
(defun badmatchlen-prove ()
  (prog2$
    (my-cw (output-file) "Running badmatchlen-prove: should fail to prove step 1.~%")
    (proof-check (output-file) nil (badsublenr) (badmatchlenp) nil nil 0)))

(defun badmatchlen2p ()
  '((1 (f a b) rule nil nil)))
(defun badmatchlen2-prove ()
  (prog2$
    (my-cw (output-file) "Running badmatchlen2-prove: should fail to prove step 1.~%")
    (proof-check (output-file) nil (badsublenr) (badmatchlen2p) nil nil 0)))

(defun badsubsp ()
  '((1 (= a a) =refl ((x b) (x a)) nil)))
(defun badsubs-prove ()
  (prog2$
    (my-cw (output-file) "Running badsubs-prove: should report bad substitutions (not just proof failure!).~%")
    (proof-check (output-file) nil (rules1) (badsubsp) nil nil 0)))

(defun nosamematchp ()
  '((1 (= a b) =refl nil nil)))
(defun nosamematch-prove ()
  (prog2$
    (my-cw (output-file) "Running nosamematch-prove: should fail to prove step 1.~%")
    (proof-check (output-file) nil (rules1) (nosamematchp) nil nil 0)))

(defun notanumberp ()
  '((1 (= (* a 0) 0) nil nil nil)))
(defun notanumber-prove ()
  (prog2$
    (my-cw (output-file) "Running notanumber-prove: should say a is not a number.~%")
    (proof-check (output-file) nil (rules9) (notanumberp) nil nil 0)))

(defun notastringp ()
  '((1 (isString xyz) nil nil nil)))
(defun notastring-prove ()
  (prog2$
    (my-cw (output-file) "Running notastring-prove: should say xyz is not a string.~%")
    (proof-check (output-file) nil (rules9) (notastringp) nil nil 0)))

(defun nosearchp ()
  '((2 (-*> B [ [ B ] ]) nil nil nil)))
(defun nosearch-prove ()
  (prog2$
    (my-cw (output-file) "Running nosearch-prove: should fail without mentioning recursion depth.~%")
    (proof-check (output-file) (assumptions5b) (rules5b) (nosearchp) '(B [ ]) nil 0)))

(defun insufficientdepthp ()
  '((4 (-*> B [ [ [ B ] B ] ]) nil nil nil)
    (7 (-*> B [ [ [ ] [ ] ] ]) nil nil nil)))
(defun insufficientdepth-prove ()
  (prog2$
    (my-cw (output-file) "Running insufficientdepth-prove: should fail with recursion depth 2.~%")
    (proof-check (output-file) (assumptions5b) (rules5b) (insufficientdepthp) '(B [ ]) nil 2)))

(defun missedgoal-prove ()
  (prog2$
    (my-cw (output-file) "Running missedgoal-prove: should say proof was successful, but you have not proved the goal.~%")
    (verify-proof (output-file) '(= (g (f c) a) (g (f a) b)) (assumptions1) (rules1) (proof1) nil '(r s a) 0)))

; Run all good tests
(defun check-good ()
  (cond ((not (prove1)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 1 failed.~%") nil))
        ((not (prove1-goal)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 1 with goal failed.~%") nil))
        ((not (prove1-auto)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 1 with step skipping failed.~%") nil))
        ((not (prove2)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 2 failed.~%") nil))
        ((not (prove2-auto)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 2 with step skipping failed.~%") nil))
        ((not (prove3)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 3 failed.~%") nil))
        ((not (prove4)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 4 failed.~%") nil))
        ((not (prove5)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 5 failed.~%") nil))
        ((not (prove5b)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 5b failed.~%") nil))
        ((not (prove6)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 6 failed.~%") nil))
        ((not (prove6b)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 6b failed.~%") nil))
        ((not (prove7)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 7 failed.~%") nil))
        ((not (prove8)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 8 failed.~%") nil))
        ((not (prove9)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 9 failed.~%") nil))
        ((not (prove10)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 10 failed.~%") nil))
        ((not (prove11)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 11 failed.~%") nil))
        ((not (prove12)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 12 failed.~%") nil))
        ((not (prove13)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 13 failed.~%") nil))
        ((not (prove13-auto)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 13 with step skipping failed.~%") nil))
        ((not (prove13-auto2)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 13 with step skipping and large search depth failed.~%") nil))
        ((not (prove14)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 14 failed.~%") nil))
        ((not (prove14-auto)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 14 with step skipping failed.~%") nil))
        ((not (prove15-auto)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 15 with step skipping failed.~%") nil))
        (T (prog2$ (my-cw (output-file) "~%SUCCESS: All good tests passed.~%") T))))

; Run all bad tests
(defun check-bad ()
  (cond ((badalist-prove) (prog2$ (my-cw (output-file) "~%ERROR: badalist passed, but it should have failed.~%") nil))
        ((badalist2-prove) (prog2$ (my-cw (output-file) "~%ERROR: badalist2 passed, but it should have failed.~%") nil))
        ((dupnames-prove) (prog2$ (my-cw (output-file) "~%ERROR: dupnames passed, but it should have failed.~%") nil))
        ((forbiddensub-prove) (prog2$ (my-cw (output-file) "~%ERROR: forbiddensub passed, but it should have failed.~%") nil))
        ((nummap-prove) (prog2$ (my-cw (output-file) "~%ERROR: nummap passed, but it should have failed.~%") nil))
        ((badruleslen1-prove) (prog2$ (my-cw (output-file) "~%ERROR: badruleslen1 passed, but it should have failed.~%") nil))
        ((badruleslen2-prove) (prog2$ (my-cw (output-file) "~%ERROR: badruleslen2 passed, but it should have failed.~%") nil))
        ((badassumplena-prove) (prog2$ (my-cw (output-file) "~%ERROR: badassumplena passed, but it should have failed.~%") nil))
        ((badassumpstmt-prove) (prog2$ (my-cw (output-file) "~%ERROR: badassumpstmt passed, but it should have failed.~%") nil))
        ((defconst-prove) (prog2$ (my-cw (output-file) "~%ERROR: defconst passed, but it should have failed.~%") nil))
        ((atomkey-prove) (prog2$ (my-cw (output-file) "~%ERROR: atomkey passed, but it should have failed.~%") nil))
        ((missingassump-prove) (prog2$ (my-cw (output-file) "~%ERROR: missingassump passed, but it should have failed.~%") nil))
        ((badstrvars-prove) (prog2$ (my-cw (output-file) "~%ERROR: badstrvars passed, but it should have failed.~%") nil))
        ((badstrvars2-prove) (prog2$ (my-cw (output-file) "~%ERROR: badstrvars2 passed, but it should have failed.~%") nil))
        ((nomatch-prove) (prog2$ (my-cw (output-file) "~%ERROR: nomatch passed, but it should have failed.~%") nil))
        ((nomatch2-prove) (prog2$ (my-cw (output-file) "~%ERROR: nomatch2 passed, but it should have failed.~%") nil))
        ((nomatch3-prove) (prog2$ (my-cw (output-file) "~%ERROR: nomatch3 passed, but it should have failed.~%") nil))
        ((badsublen-prove) (prog2$ (my-cw (output-file) "~%ERROR: badsublen passed, but it should have failed.~%") nil))
        ((badsublen2-prove) (prog2$ (my-cw (output-file) "~%ERROR: badsublen2 passed, but it should have failed.~%") nil))
        ((badmatchlen-prove) (prog2$ (my-cw (output-file) "~%ERROR: badmatchlen passed, but it should have failed.~%") nil))
        ((badmatchlen2-prove) (prog2$ (my-cw (output-file) "~%ERROR: badmatchlen2 passed, but it should have failed.~%") nil))
        ((badsubs-prove) (prog2$ (my-cw (output-file) "~%ERROR: badsubs passed, but it should have failed.~%") nil))
        ((nosamematch-prove) (prog2$ (my-cw (output-file) "~%ERROR: nosamematch passed, but it should have failed.~%") nil))
        ((notanumber-prove) (prog2$ (my-cw (output-file) "~%ERROR: notanumber passed, but it should have failed.~%") nil))
        ((notastring-prove) (prog2$ (my-cw (output-file) "~%ERROR: notastring passed, but it should have failed.~%") nil))
        ((nosearch-prove) (prog2$ (my-cw (output-file) "~%ERROR: nosearch passed, but it should have failed.~%") nil))
        ((insufficientdepth-prove) (prog2$ (my-cw (output-file) "~%ERROR: insufficientdepth passed, but it should have failed.~%") nil))
        ((missedgoal-prove) (prog2$ (my-cw (output-file) "~%ERROR: missedgoal passed, but it should have failed.~%") nil))
        (T (prog2$ (my-cw (output-file) "~%SUCCESS: All bad tests failed.~%") T))))

(defun check-long ()
  (cond ((not (prove5b-auto)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 5b with step skipping failed.~%") nil))
;        ((not (prove5b-auto-full)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 5b with full step skipping failed.~%") nil)) ; Disabled, see test
        ((not (prove6b-auto)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 6 with step skipping failed.~%") nil))
;        ((not (prove6b-auto-full)) (prog2$ (my-cw (output-file) "~%ERROR: Proof 6b with full step skipping failed.~%") nil)) ; Disabled, see test
        (T (prog2$ (my-cw (output-file) "~%SUCCESS: All long-running tests passed.~%") T))))

;;; RUN ALL TESTS ;;;
(defun check-all ()
  (if (and (check-good) (check-bad))
    (prog2$ (my-cw (output-file) "~%SUCCESS: All tests passed.~%") T)
    nil))
