(in-package "ACL2")
(program)
(include-book "proof-checker")
(include-book "my-cw")

; Print everything to console
(defmacro output-file ()
  nil)

(defun fullproofrules ()
  '((PP (implies (and (=> P Q) P) Q))
    (TT1 (implies (=> P Q) (=> (~ Q) (~ P))))         ; Can search
    (TT2 (implies (and (=> P Q) (~ Q)) (~ P)))
    (TP1 (=> (_and (_or P Q) (~ P)) Q))
    (TP2 (=> (_and (_or P Q) (~ Q)) P))
    (TP3 (implies (_or P Q) (=> (~ P) Q)))            ; Can search
    (TP4 (implies (_or P Q) (=> (~ Q) P)))            ; Can search
    (TP5 (implies (~ P) (=> (_or P Q) Q)))            ; Can search
    (TP6 (implies (~ Q) (=> (_or P Q) P)))            ; Can search
    (TP7 (implies (and (_or P Q) (~ P)) Q))
    (TP8 (implies (and (_or P Q) (~ Q)) P))
    (DN1 (=> P (~ (~ P))))
    (DN2 (=> (~ (~ P)) P))
    (DN3 (implies P (~ (~ P))))                       ; Can search
    (DN4 (implies (~ (~ P)) P))                       ; Can search
    (S1 (=> (_and P Q) P))
    (S2 (=> (_and P Q) Q))
    (S3 (implies (_and P Q) P))
    (S4 (implies (_and P Q) Q))
    (A1 (implies P (=> Q (_and P Q))))                ; Can search
    (A2 (implies P (=> Q (_and Q P))))                ; Can search
    (A3 (implies (and P Q) (_and P Q)))               ; Can search
    (HS (implies (and (=> P Q) (=> Q R)) (=> P R)))
    (LA1 (=> P (_or P Q)))
    (LA2 (=> Q (_or P Q)))
    (LA3 (implies P (_or P Q)))                       ; Can search
    (LA4 (implies Q (_or P Q)))                       ; Can search
    (DL1 (=> (_and P Q) (~ (_or (~ P) (~ Q)))))
    (DL2 (=> (~ (_and P Q)) (_or (~ P) (~ Q))))
    (DL3 (=> (_or P Q) (~ (_and (~ P) (~ Q)))))
    (DL4 (=> (~ (_or P Q)) (_and (~ P) (~ Q))))
    (DL5 (implies (_and P Q) (~ (_or (~ P) (~ Q)))))  ; Can search
    (DL6 (implies (~ (_and P Q)) (_or (~ P) (~ Q))))  ; Can search
    (DL7 (implies (_or P Q) (~ (_and (~ P) (~ Q)))))  ; Can search
    (REFL (=> A A))
    (DP1 (=> (_or P P) P))
    (DP2 (implies (_or P P) P))                       ; Can search
    (DS1 (implies (and (=> P R) (=> Q S)) (=> (_or P Q) (_or R S))))  ; Can search
    (DS2 (implies (and (=> P R) (=> Q S)) (=> (_or P Q) (_or S R))))  ; Can search
    (DS3 (implies (and (=> P R) (=> Q S) (_or P Q)) (_or R S)))
    (DS4 (implies (and (=> P R) (=> Q S) (_or P Q)) (_or S R)))
    (CL1 (=> (_and P Q) (_and Q P)))
    (CL2 (=> (_or P Q) (_or Q P)))
    (CL3 (implies (_and P Q) (_and Q P)))             ; Can search
    (CL4 (implies (_or P Q) (_or Q P)))               ; Can search
    (LB1 (implies (<=> P Q) (=> P Q)))                ; Can search
    (LB2 (implies (<=> P Q) (=> Q P)))                ; Can search
    (LB3 (implies (and (=> P Q) (=> Q P)) (<=> P Q))) ; Can search
    (LB4a (implies (<=> P Q) (=> P Q)))               ; Can search
    (LB4b (implies (<=> P Q) (=> Q P)))))             ; Can search
(defun pp_proofrules ()
  '((PP (implies (and (=> P Q) P) Q))
    (TT (implies (=> P Q) (=> (~ Q) (~ P))))
    (TP1 (=> (_and (_or P Q) (~ P)) Q))
    (TP2 (=> (_and (_or P Q) (~ Q)) P))
    (DN1 (=> P (~ (~ P))))
    (DN2 (=> (~ (~ P)) P))
    (S1 (=> (_and P Q) P))
    (S2 (=> (_and P Q) Q))
    (A1 (implies P (=> Q (_and P Q))))
    (A2 (implies Q (=> P (_and P Q))))
    (HS (implies (and (=> P Q) (=> Q R)) (=> P R)))
    (LA1 (=> P (_or P Q)))
    (LA2 (=> Q (_or P Q)))
    (DL1 (=> (_and P Q) (~ (_or (~ P) (~ Q)))))
    (DL2 (=> (~ (_and P Q)) (_or (~ P) (~ Q))))
    (DL3 (=> (_or P Q) (~ (_and (~ P) (~ Q)))))
    (DL4 (=> (~ (_or P Q)) (_and (~ P) (~ Q))))
    (DL_R1 (implies (=> P R) (=> (_or P Q) (_or R Q))))
    (DL_R2 (implies (=> P R) (=> (_and P Q) (_and R Q))))
    (DP (=> (_or P P) P))
    (DS1 (implies (and (=> P R) (=> Q S)) (=> (_or P Q) (_or R S))))
    (DS2 (implies (and (=> P R) (=> Q S)) (=> (_or P Q) (_or S R))))
    (CL1 (=> (_and P Q) (_and Q P)))
    (CL2 (=> (_or P Q) (_or Q P)))
    (LB1 (implies (<=> P Q) (=> P Q)))
    (LB2 (implies (<=> P Q) (=> Q P)))
    (LB3 (implies (_and (=> P Q) (=> Q P)) (<=> P Q)))
    (LB4a (implies (<=> P Q) (=> P Q)))
    (LB4b (implies (<=> P Q) (=> Q P)))))

(defun assumptions_logic1 ()
  '((assumption1 (=> T (_and A B)))
    (assumption2 T)
    (assumption3 (=> (~ P) (~ A)))
    (assumption4 (_or (~ B) Q))
    (assumption5 (~ R))
    (assumption6 (=> (_or W (~ S)) R))))

(defun proof_logic1_full ()
  '((P02 (~ (_or W (~ S))) nil nil nil)
    (P03 (_and A B) nil nil nil)
    (P05 A nil nil nil)                               ; Can skip
    (P07 (~ (~ A)) nil nil nil)
    (P09 (~ (~ P)) nil nil nil)                       ; Can skip
    (P11 P nil nil nil)                               ; Can skip
    (P13 B nil nil nil)                               ; Can skip
    (P15 (~ (~ B)) nil nil nil)
    (P19 Q nil nil nil)                               ; Can skip
    (P21 (_and P Q) nil nil nil)                      ; Can skip
    (P22 (=> (~ S) (_or W (~ S))) nil nil nil)
    (P24 (~ (~ S)) nil nil nil)                       ; Can skip
    (P26 S nil nil nil)                               ; Can skip
    (P28 (_or S C) nil nil nil)                       ; Can skip
    (P30 (_and (_and P Q) (_or S C)) nil nil nil)))
(defun prove_logic1_full ()
  (prog2$
    (my-cw (output-file) "RUNNING: prove_logic1_full...~%")
    (proof-check (output-file) (assumptions_logic1) (fullproofrules) (proof_logic1_full) nil nil 0)))

(defun proof_logic1_pp ()
  '((P01 (=> (~ R) (~ (_or W (~ S)))) nil nil nil)
    (P02 (~ (_or W (~ S))) nil nil nil)
    (P03 (_and A B) nil nil nil)
    (P04 (=> (_and A B) A) nil nil nil)
    (P05 A nil nil nil)
    (P06 (=> A (~ (~ A))) nil nil nil)
    (P07 (~ (~ A)) nil nil nil)
    (P08 (=> (~ (~ A)) (~ (~ P))) nil nil nil)
    (P09 (~ (~ P)) nil nil nil)
    (P10 (=> (~ (~ P)) P) nil nil nil)
    (P11 P nil nil nil)
    (P12 (=> (_and A B) B) nil nil nil)
    (P13 B nil nil nil)
    (P14 (=> B (~ (~ B))) nil nil nil)
    (P15 (~ (~ B)) nil nil nil)
    (P16 (=> (~ (~ B)) (_and (_or (~ B) Q) (~ (~ B)))) nil nil nil)
    (P17 (_and (_or (~ B) Q) (~ (~ B))) nil nil nil)
    (P18 (=> (_and (_or (~ B) Q) (~ (~ B))) Q) nil nil nil)
    (P19 Q nil nil nil)
    (P20 (=> Q (_and P Q)) nil nil nil)
    (P21 (_and P Q) nil nil nil)
    (P22 (=> (~ S) (_or W (~ S))) nil nil nil)
    (P23 (=> (~ (_or W (~ S))) (~ (~ S))) nil nil nil)
    (P24 (~ (~ S)) nil nil nil)
    (P25 (=> (~ (~ S)) S) nil nil nil)
    (P26 S nil nil nil)
    (P27 (=> S (_or S C)) nil nil nil)
    (P28 (_or S C) nil nil nil)
    (P29 (=> (_and P Q) (_and (_and P Q) (_or S C))) nil nil nil)
    (P30 (_and (_and P Q) (_or S C)) nil nil nil)))
(defun prove_logic1_pp ()
  (prog2$
    (my-cw (output-file) "RUNNING: prove_logic1_pp...~%")
    (proof-check (output-file) (assumptions_logic1) (pp_proofrules) (proof_logic1_pp) nil nil 0)))

(defun assumptions_logic2 ()
  '((assumption1 (=> R N))
    (assumption2 (=> K (_or B R)))
    (assumptions3 (=> (_or Q M) K))
    (assumption4 (~ N))))

(defun proof_logic2_full ()
  '((P02 (~ R) nil nil nil)
    (P03 (=> (~ B) (_and (~ B) (~ R))) nil nil nil)
    (P04a (=> (_or B R) (~ (_and (~ B) (~ R)))) nil nil nil)
    (P04b (=> (~ (~ (_and (~ B) (~ R)))) (~ (_or B R))) nil nil nil)
    (P04c (=> (_and (~ B) (~ R)) (~ (~ (_and (~ B) (~ R))))) nil nil nil)
    (P04d (=> (_and (~ B) (~ R)) (~ (_or B R))) nil nil nil)
    (P05 (=> (~ B) (~ (_or B R))) nil nil nil)
    (P06 (=> (~ (_or B R)) (~ K)) nil nil nil)
    (P07 (=> (~ B) (~ K)) nil nil nil)
    (P08 (=> (~ K) (~ (_or Q M))) nil nil nil)
    (P09 (=> (~ B) (~ (_or Q M))) nil nil nil)
    (P10 (=> (~ (_or Q M)) (_and (~ Q) (~ M))) nil nil nil)
    (P11 (=> (~ B) (_and (~ Q) (~ M))) nil nil nil)
    (P12 (=> (_and (~ Q) (~ M)) (~ Q)) nil nil nil)
    (P13 (=> (~ B) (~ Q)) nil nil nil)))
(defun prove_logic2_full ()
  (prog2$
    (my-cw (output-file) "RUNNING: prove_logic2_full...~%")
    (proof-check (output-file) (assumptions_logic2) (fullproofrules) (proof_logic2_full) nil nil 0)))

(defun proof_logic2_pp ()
  '((P01 (=> (~ N) (~ R)) nil nil nil)
    (P02 (~ R) nil nil nil)
    (P03 (=> (~ B) (_and (~ B) (~ R))) nil nil nil)
    (P04a (=> (_or B R) (~ (_and (~ B) (~ R)))) nil nil nil)
    (P04b (=> (~ (~ (_and (~ B) (~ R)))) (~ (_or B R))) nil nil nil)
    (P04c (=> (_and (~ B) (~ R)) (~ (~ (_and (~ B) (~ R))))) nil nil nil)
    (P04d (=> (_and (~ B) (~ R)) (~ (_or B R))) nil nil nil)
    (P05 (=> (~ B) (~ (_or B R))) nil nil nil)
    (P06 (=> (~ (_or B R)) (~ K)) nil nil nil)
    (P07 (=> (~ B) (~ K)) nil nil nil)
    (P08 (=> (~ K) (~ (_or Q M))) nil nil nil)
    (P09 (=> (~ B) (~ (_or Q M))) nil nil nil)
    (P10 (=> (~ (_or Q M)) (_and (~ Q) (~ M))) nil nil nil)
    (P11 (=> (~ B) (_and (~ Q) (~ M))) nil nil nil)
    (P12 (=> (_and (~ Q) (~ M)) (~ Q)) nil nil nil)
    (P13 (=> (~ B) (~ Q)) nil nil nil)))
(defun prove_logic2_pp ()
  (prog2$
    (my-cw (output-file) "RUNNING: prove_logic2_pp...~%")
    (proof-check (output-file) (assumptions_logic2) (pp_proofrules) (proof_logic2_pp) nil nil 0)))

(defun runalltests ()
  (cond ((not (prove_logic1_full)) (my-cw (output-file) "~%ERROR: Proof 1 with full rule set failed.~%"))
        ((not (prove_logic1_pp)) (my-cw (output-file) "~ERROR: Proof 1 with reduced rule set failed.~%"))
        ((not (prove_logic2_full)) (my-cw (output-file) "~%ERROR: Proof 2 with full rule set failed.~%"))
        ((not (prove_logic2_pp)) (my-cw (output-file) "~ERROR: Proof 2 with reduced rule set failed.~%"))
        (T (prog2$ (my-cw (output-file) "~%SUCCESS: All logic tests passed.~%") T))))
