 (
 (1 (input) (or (animal v0) (not (wolf v0))) (1))
 (2 (input) (or (animal v0) (not (fox v0))) (2))
 (3 (input) (or (animal v0) (not (bird v0))) (3))
 (4 (input) (or (animal v0) (not (snail v0))) (5))
 (5 (input) (or (plant v0) (not (grain v0))) (6))
 (6 (input) (or (eats v0 v1) (or (eats v0 v2) (or (not (animal v0)) (or (not (plant v1)) (or (not (animal v2)) (or (not (plant v3)) (or (not (much_smaller v2 v0)) (not (eats v2 v3))))))))) (7))
 (7 (input) (or (much_smaller v0 v1) (or (not (snail v0)) (not (bird v1)))) (9))
 (8 (input) (or (much_smaller v0 v1) (or (not (bird v0)) (not (fox v1)))) (10))
 (9 (input) (or (much_smaller v0 v1) (or (not (fox v0)) (not (wolf v1)))) (11))
 (10 (input) (or (not (wolf v0)) (or (not (grain v1)) (not (eats v0 v1)))) (13))
 (11 (input) (or (not (bird v0)) (or (not (snail v1)) (not (eats v0 v1)))) (15))
 (12 (input) (or (plant (snail_food_of v0)) (not (snail v0))) (18))
 (13 (input) (or (eats v0 (snail_food_of v0)) (not (snail v0))) (19))
 (14 (input) (or (not (animal v0)) (or (not (animal v1)) (or (not (grain v2)) (or (not (eats v0 v1)) (not (eats v1 v2)))))) (20))
 (15 (instantiate 6 ((v1 . v3))) (or (eats v0 v3) (or (eats v0 v2) (or (not (animal v0)) (or (not (plant v3)) (or (not (animal v2)) (or (not (plant v3)) (or (not (much_smaller v2 v0)) (not (eats v2 v3))))))))) NIL)


(defun term2miz (term)
; like fla2miz on atomic flas, but dieffrent collecting
; leaving it to return empty preds list too,
; since we may need it later for Fraenkels
(let ((res "") vars preds funcs)
  (cond ((listp term)
	 (let (prev (ress (mapcar 'term2miz (cdr term))))
	   (setq res (symbol-name (car term)))
	   (if (string-match "^v[0-9]+$" res)
	       (error (concat "Var here!: " res))
	     (setq funcs (list res)))
	   (if ress (setq res (concat res "(") prev t))
	   (while ress
	     (setq res (concat res (caar ress))
	     vars (union vars (second (car ress)))
	     preds (union preds (third (car ress)))
	     funcs (union funcs (fourth (car ress)))
	     ress (cdr ress))
	     (if ress (setq res (concat res ","))))
	   (if prev (setq res (concat res ")")))
	   ))
	(t (setq res (symbol-name term))
	   (if (string-match "^v[0-9]+$" res)
	       (setq vars (list res))
	     (setq funcs (list res)))))
  (list res vars preds funcs)))


       
(defun fla2miz (fla)
;"Input is either one symbol (false) or list.
;(or a b) --> (a or b),(f a b) --> f(a,b),(not a)-->(not a),(P a b) --> P(a,b),"
; collect vars,preds and funcs here
; 0-arity preds and funcs are always wrapped in (),
; that's the way to recognize variables.
; Generally, the names can be oveloaded (v7 can be a predicate) -
; we have to rename for Mizar - later.
  (let ((res "") vars preds funcs)
    (cond ((listp fla)
	   (cond ((eq 'or (car fla)) 
		  (let ((res1 (fla2miz (cadr fla)))
			(res2 (fla2miz (caddr fla))))
		    (setq res (concat (car res1) " or " (car res2))
			  vars (union (cadr res1) (cadr res2))
			  preds (union (third res1) (third res2) :test 'equal)
			  funcs (union (fourth res1) (fourth res2) :test 'equal)
			  )))
		 ((eq 'not (car fla))
		  (let ((res1 (fla2miz (cadr fla))))
		    (setq res (concat  " not " (car res1))
			  vars (cadr res1)
			  preds (third res1)
			  funcs (fourth res1)
			  )))
	       ;;; predicate or list
		 (t
		  (let (prev (ress (mapcar 'term2miz (cdr fla))))
		    (setq res (symbol-name (car fla)))
		    (if (string-match "^v[0-9]+$" res)
			(error (concat "Var here!: " res))
		      (setq preds (list (cons res (length (cdr fla))))))
					; not for mizar predicates
;		    (if ress (setq res (concat res "(") prev t))
		    (while ress
		      (setq res (concat res (caar ress))
			    vars (union vars (second (car ress)))
			    preds (union preds (third (car ress)) :test 'equal)
			    funcs (union funcs (fourth (car ress)) :test 'equal)
			    ress (cdr ress))
		      (if ress (setq res (concat res ","))))
					; not for mizar predicates
;		    (if prev (setq res (concat res ")")))
		    ))))
	  ((symbolp fla)
	   (if (eq fla 'false)
	       (setq res "contradiction")
	     (error (concat "Bad fla here!: " (symbol-name fla)))))
	  (t (setq res (symbol-name fla))
	      (if (string-match "^v[0-9]+$" res)
		  (error (concat "Var here!: " res))
		(setq preds (list res)))))
    (list res vars preds funcs)))



(defun translate (otter-list)
"Translate a piece of Otter proof object into Mizar,
return list of Mizar steps. and lists of vars,preds and funcs used.
Input clauses have no justification,
Instantiate steps are justified by their parent,
Resolve steps are justified by parents,
Propsitional by parents.
"
(let (out allvars allpreds allfuncs)
  (while otter-list
    (let* ((in (car otter-list))
	   (mylab (concat "A" (int-to-string (car in)) ": "))
	   (justif (cadr in))
	   (rule (car justif))
	   (refs (delete-if 'listp (copy-sequence 
				    (cdr justif))))  ; don't need literals
	   (factandsyms (fla2miz (caddr in)))
	   (vars (second factandsyms))
	   (preds (third factandsyms))
	   (funcs (fourth factandsyms))
	   (varsstr (mapconcat 'identity vars ","))
	   (fact (if vars (concat "for " varsstr " holds " (car factandsyms))
		   (car factandsyms)))
	   (res (concat mylab fact)))
      (if refs
	  (setq res (concat res " by " 
			    (mapconcat '(lambda (x) (concat "A" (int-to-string x)))
				       refs ","))))
      (setq  res (concat res ";\n")
	     otter-list (cdr otter-list)
	     allvars (union vars allvars)
	     allpreds (union preds allpreds)
	     allfuncs (union funcs allfuncs)
	     out (cons res out))))
  (list (nreverse out) allvars allpreds allfuncs)))

(defvar  translation-header 
":: Article created automatically from Otter proof object
:: by ott2miz
environ
")

(defun ott2miz (otter-list articlename)
"Prints the .miz and .voc file for the proof object"
(let* ((trans (translate otter-list))
       (steps (car trans))
       (vars  (second trans))
       (preds (third trans))
       (funcs (fourth trans))
       (mizbuf (find-file-noselect (concat articlename ".miz")))
       (vocbuf (find-file-noselect (concat articlename ".voc"))))
  (with-current-buffer mizbuf
    (erase-buffer)
    (insert translation-header)
    (insert "vocabulary " articlename ";\n" "begin\n\n")
    (if vars 
	(insert "reserve " (mapconcat 'identity vars ",") "\n for set;\n\n"))
    (while steps 
      (insert (car steps))
      (setq steps (cdr steps)))
    (save-buffer))
  (with-current-buffer vocbuf
    (erase-buffer)
    (while funcs 
      (insert "O" (car funcs) "\n")
      (setq funcs (cdr funcs)))
    (while preds 
      (insert "R" (car preds) "\n")
      (setq preds (cdr preds)))
    (save-buffer))
  ))
