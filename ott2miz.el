;; ott2miz - otter to Mizar translator
;; $Revision: 1.18 $
;; run with: emacs -batch -q -l ott2miz.el --eval '(translate-many "<indexfile>")'
;; where <indexfile> is in a directory with all problems (proof objects),
;; and it contains listing of their filenames (without directory)
;; results in .miz and .voc file for each problem.
;; Special mappings to Mizar symbols can be given for each file
;; in a rule file with extension .rul .
;; The rules must have the form:
;;
;; ("OTTER-SYMBOL" MIZAR-PATTERN)
;;
;; where MIZAR-PATTERN looks e.g. like (1 "=" 2),
;; i.e. the arguments are given by numbers, and the rest are supposed
;; to be Mizar symbols and interpunction.
;; Actually, this can
;; be used to expand to complex terms too, e.g. to
;; ("+(" 1 "," "-(" 2 "))" )

;; Note that symbols captured by these rules will not
;; be defined in the vocabulary and introduced via contradiction,
;; you will have to write the environmental directives manually for them.

;; We now use global hashes for symbols -
;; requires Emacs v. >= 21

(require 'cl)

(setq max-lisp-eval-depth 2000)
(setq max-specpdl-size 2000)

(defvar mizar-syms '(and antonym attr as assume be begin being canceled case cases cluster coherence compatibility consider consistency constructors contradiction correctness clusters def deffunc definition definitions defpred environ equals ex existence for func given hence  requirements holds if iff implies irreflexivity it let means mode not notation notations of or otherwise  over per pred provided qua reconsider redefine reflexivity reserve scheme schemes signature struct such suppose synonym take that thus then theorems vocabularies where associativity commutativity connectedness irreflexivity reflexivity symmetry uniqueness transitivity idempotence asymmetry projectivity involutiveness by from proof now end hereby for ex not & or implies iff st holds being theorem scheme definition thesis empty in))






(defun int-or-symbol-name (obj)
(if (symbolp obj) (symbol-name obj)
  (int-to-string obj)))

(defun hash-vals (hsh)
(let (l) 
  (maphash (function (lambda (key val) (setq l (cons val l)))) hsh)
  l))

(defun obj-from-path (from path)
"Given a path, select the corresponding object in sexp 'from'"
(while path
  (setq from (nth (car path) from)
	path (cdr path)))
from)


(defconst varkind 0)
(defconst predkind 1)
(defconst funckind 2)
(defconst locikind 3)
(defconst mizkind 4)

(defun sgn-insert (obj sign kind &optional arity)
"Insert symbol or int into a signature, fix possible clashes.
Kind is 0 ('var), 1('pred), 2 ('func) .
Returns the string created."
(let ((res (gethash obj (elt sign kind))))
  (if res (if arity (car res) res)
    (let ((name (int-or-symbol-name obj)))
      (if (or (gethash obj (elt sign varkind))
	      (gethash obj (elt sign predkind))
	      (gethash obj (elt sign funckind))
	      (gethash obj (elt sign locikind))
	      (gethash obj (elt sign mizkind)))	 
	  (setq name (concat name "__" (int-to-string kind))))
      (puthash obj (if arity (cons name arity) name)
	       (elt sign kind))
      name))))

(defun parse-rules (fname)
(when (file-readable-p fname)
  (let ((res (makehash)) tab)
    (with-temp-buffer
      (insert-file-contents-literally fname)
      (goto-char (point-min))
      (insert "(")
      (goto-char (point-max))
      (insert ")")
      (goto-char (point-min))
      (setq tab (read (current-buffer))))
    (dolist (r1 tab) (puthash (intern (car r1)) (second r1) res))
    res)))

(defun create-name-hash (syms)
(let ((res (make-hash-table :size (length syms))))
  (while syms 
    (puthash (car syms) (symbol-name (car syms)) res)
    (setq syms (cdr syms)))
  res))
  
(defun rule-use (rules sym args kind)
"Use a rule from RULES creating string from SYM and ARGS.
The rule must exist at this point."
(let ((rule (gethash sym rules)))
  (mapconcat '(lambda (x) (if (stringp x) x (car (nth (- x 1) args))))
	     rule "")))

(defun rule-exists (rules sym kind &optional arity)
(if rules (gethash sym rules)))

(defun term2miz (term sign rules)
;; like fla2miz on atomic flas, but dieffrent collecting
"Return list (TERMSTR VARS), where TERMSTR is the Mizar 
representation of the term, and VARS are variables inside it."
(let ((res "") vars preds funcs)
  (cond 
   ((listp term)
    (let ((ress (mapcar '(lambda (x) (term2miz x sign rules)) (cdr term))))
      (dolist (r1 ress) (setq vars (union vars (second r1))))
      (if (rule-exists rules (car term) funckind (length (cdr term)))
	  (setq res (rule-use rules (car term) ress funckind))
	(setq res (sgn-insert (car term) sign funckind 
			      (length (cdr term))))
	(if ress 
	    (setq res (concat res "(" (mapconcat 'car ress ",") ")" ))))))
   ((symbolp term)
    (setq res (sgn-insert term sign varkind)
	  vars (list res)))
   (t (error (concat "Bad term here!: " (prin1-to-string term)))))
  (list res vars)))
       
(defun fla2miz (fla sign rules)
  ;;"Input is either one symbol (false) or list.
  ;;(or a b) --> (a or b),(f a b) --> f(a,b),(not a)-->(not a),(P a b) --> P(a,b),"
  ;; collect vars,preds and funcs here
  ;; 0-arity preds and funcs are always wrapped in (),
  ;; that's the way to recognize variables.
  ;; Generally, the names can be oveloaded (v7 can be a predicate) -
  ;; we have to rename for Mizar - later.
  (let ((res "") vars preds funcs)
    (cond 
     ((listp fla)
      (cond 
       ((eq 'or (car fla)) 
	(let ((res1 (fla2miz (cadr fla) sign rules))
	      (res2 (fla2miz (caddr fla) sign rules)))
	  (setq res (concat (car res1) " or " (car res2))
		vars (union (cadr res1) (cadr res2))
		)))
       ((eq 'not (car fla))
	(let ((res1 (fla2miz (cadr fla) sign rules)))
	  (setq res (concat  " not " (car res1))
		vars (cadr res1)
		)))
       ((eq 'equal (car fla)) 
	(let ((res1 (term2miz (cadr fla) sign rules))
	      (res2 (term2miz (caddr fla) sign rules)))
	  (setq res (concat (car res1) " = " (car res2))
		vars (union (cadr res1) (cadr res2))
		)))
	       ;;; predicate or list
       (t
	(let ((ress (mapcar '(lambda (x) (term2miz x sign rules)) (cdr fla))))
	  (dolist (r1 ress) (setq vars (union vars (second r1))))
	  (if (rule-exists rules (car fla) predkind (length (cdr fla)))
	      (setq res (rule-use rules (car fla) ress predkind))
	    (setq res (sgn-insert (car fla) sign predkind 
					  (length (cdr fla))))
	    ;; no "(" ")" for mizar predicates
	    (if ress (setq res (concat res " " 
				       (mapconcat 'car ress ",")))))))))
     ((symbolp fla)
      (if (eq fla 'false)
	  (setq res "contradiction")
	(error (concat "Bad fla here!: " (symbol-name fla)))))
     (t (error (concat "Bad fla here!: " (prin1-to-string fla)))))
    (list res vars)))



(defun translate (orig-list sign rules)
  "Translate a piece of Otter proof object into Mizar,
return list of Mizar steps. and lists of vars,preds and funcs used.
Input clauses have no justification,
Instantiate steps are justified by their parent,
Resolve steps are justified by parents,
Propsitional by parents.
"
  (let ((otter-list orig-list) out assumptions)
    (while otter-list
      (let* ((in (car otter-list))
	     (mylab (concat "A" (int-to-string (car in)) ": "))
	     (justif (cadr in))
	     (rule (car justif))
	     (refs (delete-if 'listp (copy-sequence 
				      (cdr justif)))) ; don't need literals
	     (factandsyms (fla2miz (caddr in) sign rules))
	     (vars (second factandsyms))
	     (varsstr (mapconcat 'identity vars ","))
	     (fact (if vars (concat "for " varsstr " holds " (car factandsyms))
		     (car factandsyms)))
	     res)
	(cond 
	 ((eq rule 'input)
	  (setq assumptions (cons fact assumptions)
		res (concat "assume " mylab fact)))
	 ;; Resolution handling
	 ((eq rule 'resolve) ;; we need to chase only one ancestor
	  (let* ((paths (delete-if  'numberp (copy-sequence (cdr justif))))
		 (ref1 (caddr (nth (- (car refs) 1) orig-list)))
		 (lit1 (obj-from-path ref1 (car paths)))
		 (res1 (fla2miz lit1 sign rules))
		 (vars1 (second res1)))
	    (cond 
	     ((not vars1)   
	      ;; without vars, happy - simple justif
	      (setq res (concat mylab fact " by " 
				(mapconcat '(lambda (x) 
					      (concat "A" (int-to-string x)))
					   refs ","))))
	     ;; ok, the needed vars are in result
	     ((subsetp vars1 vars)   
	      (let* ((fs1 (fla2miz ref1 sign rules))
		     (restvars (set-difference (second fs1) vars))
		     (restvstr (mapconcat 'identity restvars ","))
		     (inter (if restvars 
				(concat "for " restvstr " holds " (car fs1))
			      (car fs1))))
		;; THis is a proof - hopefully
		(setq res (concat mylab fact "\nproof let " varsstr ";\n"
				  inter " by A" (int-to-string (car refs))
				  ";\nhence thesis by A" 
				  (int-to-string (second refs)) ";\nend"))))
	     ;; Redundant var - remove it by now - add a fictitious var
	     (t   
	      (let* ((letvars (union vars1 vars))
		     (letvsstr (mapconcat 'identity letvars ","))
		     (fs1 (fla2miz ref1 sign rules))
		     (restvars (set-difference (second fs1) letvars))
		     (restvstr (mapconcat 'identity restvars ","))
		     (inter (if restvars 
				(concat "for " restvstr " holds " (car fs1))
			      (car fs1))))
		(setq res (concat mylab fact "\nproof\n now let " letvsstr 
				  ";\n" inter " by A" 
				  (int-to-string (car refs)) ";\n"
				  "hence " (car factandsyms) " by A" 
				  (int-to-string (second refs)) ";\nend;\n"
				  "hence thesis;\nend")))))))
	 ;; Pramodulation handling 
	 ;; - seems that the first clause in refs is always the demodulator
	 ;; the equality must not be under any (even fictitious) quantifier,
	 ;; to do simple justif.
	 ((eq rule 'paramod) ;; we need to chase only one ancestor
	  (let* ((paths (delete-if  'numberp (copy-sequence (cdr justif))))
		 (ref1 (caddr (nth (- (car refs) 1) orig-list)))
		 (fs1 (fla2miz ref1 sign rules))
		 (fvars1 (second fs1)))
	    (cond 
	     ((not fvars1)
	      ;; without vars, happy - simple justif
	      (setq res (concat mylab fact " by " 
				(mapconcat '(lambda (x) 
					      (concat "A" (int-to-string x)))
					   refs ","))))
	     ;; ok, more vars in result than in demod
	     ((subsetp fvars1 vars)
	      (let* ((inter (car fs1)))
		;; THis is a proof - hopefully
		(setq res (concat mylab fact "\nproof let " varsstr ";\n"
				  inter " by A" (int-to-string (car refs))
				  ";\nhence thesis by A" 
				  (int-to-string (second refs)) ";\nend"))))

	     ;; Redundant var - remove it by "now" - add a fictitious var
	     (t   
	      (let* ((letvsstr (mapconcat 'identity (union fvars1 vars) ","))
		     (inter (car fs1)))
		(setq res (concat mylab fact "\nproof\n now let " letvsstr 
				  ";\n" inter " by A" 
				  (int-to-string (car refs)) ";\n"
				  "hence " (car factandsyms) " by A" 
				  (int-to-string (second refs)) ";\nend;\n"
				  "hence thesis;\nend")))))))

	 (t
	  (setq res (concat mylab fact))
	  (if refs
	  (setq res (concat res " by " 
			    (mapconcat '(lambda (x) 
					  (concat "A" (int-to-string x)))
				       refs ","))))))
	(setq  res (concat res ";\n")
	       otter-list (cdr otter-list)
	       out (cons res out))))
    (list (nreverse out) (nreverse assumptions))))

(defvar  translation-header 
  ":: Article created automatically from Otter proof object
:: by ott2miz
environ
")
(defvar def-header "definition\n")
(defvar contra-assumption "assume ASS: contradiction;\n")
(defvar def-footer "end;\n\n" )
 

(defun create-def-steps (aritylist kind sign)
"Creates a list of definitional steps, aritylist is nonempty,
kind is either 'pred' or 'func'"
(let* ((al (sort aritylist (function (lambda (x y) (< (cdr x) (cdr y))))))
       (prev 0) 
       (locivars "")
       (defbody " means not contradiction;\n")
       (justif (if (equal kind "func") "correctness by ASS;\n"
		 "correctness;\n"))
       (leftbrack "")
       (rightbrack "")
       step res)
  (while al
    (if (= prev (cdar al))
	(setq step (concat kind " " (caar al) leftbrack locivars rightbrack 
			   defbody justif)
	      res (cons step res))
      
      (let (l addedloci)
	(while (< prev (cdar al))
	  (setq l (cons (sgn-insert 
			 (intern (concat "x" (int-to-string (+ 1 prev))))
			 sign locikind)
			l)
		prev (+ 1 prev)))
	(if (equal kind "func")
	    (setq leftbrack "(" rightbrack ")"))
	(setq addedloci (mapconcat 'identity (nreverse l) ",")
	      step (concat "let " addedloci " be set;\n")
	      res (cons step res)
	      locivars (if (equal "" locivars) 
			   (concat " " addedloci)
			 (concat  locivars "," addedloci))
	      step (concat kind " " (caar al) leftbrack locivars rightbrack 
			   defbody justif)
	      res (cons step res))))
    (setq al (cdr al)))
  (nreverse res)))

(defvar max-line-length 70)

(defun mizinsert (&rest args)
"Like insert, but watches for line length"
(let ((lines (split-string (mapconcat 'identity args "") "\n")))
  (while lines
    (if (<= (length (car lines)) max-line-length)
	(insert (car lines) "\n")
      (let* ((pos (- max-line-length 1))
	     (bad (car lines))
	     (total (- (length bad) 1))
	     (start 0) (splitchar 32))
	(while (< start total)
	  (if (< (- total start) max-line-length)
	      (progn
		(insert (substring bad start) "\n")
		(setq start total))
	    (while (and (<= start  pos) (not (eq (aref bad pos) splitchar))) 
	      (decf pos))
	    (if (<= pos start) 
		(cond ((eq splitchar 32)
		       (setq splitchar 44
			     pos (min (+ start max-line-length) total)))
		      ((eq splitchar 44)
		       (setq splitchar 40
			  pos (min (+ start max-line-length) total)))
		      ((eq splitchar 40)
		       (setq splitchar 41
			  pos (min (+ start max-line-length) total)))
		      (t
		       (error (concat "Unsplittable line: " bad))))
	      (setq splitchar 32)
	      (insert (substring bad start pos) "\n")
	      (setq start pos 
		    pos (min (+ pos max-line-length) total)))))))
    (setq lines (cdr lines)))))
	      

(defun ott2miz (otter-list sign rules articlename)
  "Prints the .miz and .voc file for the proof object"
  (let* ((trans (translate otter-list sign rules))
	 (steps (car trans))
	 (vars  (car sign))
	 (preds (second sign))
	 (funcs (third sign))
	 (assumptions (second trans))
	 (mizbuf (find-file-noselect (concat articlename ".miz")))
	 (vocbuf (find-file-noselect (concat articlename ".voc"))))
;; Voc file
    (with-current-buffer vocbuf
      (erase-buffer)
      (maphash 
       (function (lambda (key val) (mizinsert "O" (car val) "\n")))
       funcs)
      (maphash 
       (function (lambda (key val) (mizinsert "R" (car val) "\n")))
       preds)
      (set-buffer-modified-p t)
      (save-buffer))
;; Miz file
    (with-current-buffer mizbuf
      (erase-buffer)
      (mizinsert translation-header)
      (mizinsert "vocabularies " (upcase articlename) ";\n" "begin\n\n")
      (if (< 0 (hash-table-count vars))
	  (mizinsert "reserve " (mapconcat 'identity (hash-vals vars) ",")
		     "\n for set;\n\n"))
;; Function defs
      (if (< 0 (hash-table-count funcs))
	  (let ((funcdefs (create-def-steps (hash-vals funcs) "func" sign)))
	    (mizinsert def-header contra-assumption)
	    (while funcdefs
	      (mizinsert (car funcdefs))
	      (setq funcdefs (cdr funcdefs)))
	    (mizinsert def-footer)))
;; Predicate defs
      (if (< 0 (hash-table-count preds))
	  (let ((preddefs (create-def-steps (hash-vals preds) "pred" sign)))
	    (mizinsert def-header contra-assumption)
	    (while preddefs
	      (mizinsert (car preddefs))
	      (setq preddefs (cdr preddefs)))
	    (mizinsert def-footer)))
;; Theorem
      (if (not assumptions) 
	  (error "No assumptions!!")
	(mizinsert "theorem\n")
	(while assumptions
	  (mizinsert "(" (car assumptions) ")"
		     (if (cdr assumptions) " &\n" 
		       "\nimplies contradiction\nproof\n"))
	  (setq assumptions (cdr assumptions))))
;; Inference steps, the last one must be thesis (contradiction)
      (while steps 
	(mizinsert (if (cdr steps) "" "thus ") (car steps))
	(setq steps (cdr steps)))
;; End of proof
      (mizinsert "end;\n")
      (set-buffer-modified-p t)
      (save-buffer))
    (kill-buffer mizbuf)
    (kill-buffer vocbuf)
    ))


(defun create-name-hash (syms)
(let ((res (make-hash-table :size (length syms))))
  (while syms 
    (puthash (car syms) (symbol-name (car syms)) res)
    (setq syms (cdr syms)))
  res))


(defvar allowed-chars "abcdefghijklopqrstuvwxyz")

(defun gen-new-name (mizname used)
"Try to generate a name which is not used."
(let ((i 0) (new (copy-sequence mizname)))
  (while (and (< i (length allowed-chars))
	      (aset new 6 (aref allowed-chars i))
	      (gethash new used))
    (incf i))
  (if (= i (length allowed-chars)) mizname
    new)))

(defvar rule-file-extension ".rul"
"Mandatory extension for syntax rule files."
)

(defun translate-file (fname &optional usednames mizsymbs)
  "Takes care of TPTP and Mizar filenames too,
if usednames given, tries to provide a new name if conflict,
if mizsymbs given, the hash of mizar syms is not created here."
  (let* ((dir (file-name-directory fname))
	 (name (file-name-nondirectory fname))
	 (name1 (file-name-sans-extension name))
	 (rname (concat (file-name-sans-extension fname)
			rule-file-extension))
	 (rules (parse-rules rname))
	 (sign  (list (makehash) (makehash) (makehash) (makehash)
		      (if mizsymbs mizsymbs 
			(create-name-hash mizar-syms)))))
    (unless (string-match "^\\([A-Z0-9_+-]+\\).*" name1)
      (error "File names must match ^[A-Z0-9_+-]+.* for creating Mizar-friendly names: %s" name1))
;;    (string-match "\\([A-Z0-9]+[+-][0-9]+\\).*" name1)
    (let ((mizname (downcase (match-string 1 name1))))
;; take care of [+-] by replacing with [pm]
      (setq mizname 
	    (replace-regexp-in-string 
	     "[+]" "p" (replace-regexp-in-string "[-]" "m" mizname)))
;;      (aset mizname 6 (if (eq (aref mizname 6) 45) 109 112))
      (if (< 8 (length mizname)) 
	  (setq mizname (substring mizname 0 8)))
      (if usednames
	  (progn
	    (if (gethash mizname usednames)
		(setq mizname (gen-new-name mizname usednames)))
	    (puthash mizname name1 usednames)))
      (with-temp-buffer
	(insert-file-contents-literally fname)
	(goto-char (point-min))
	(ott2miz (read (current-buffer)) sign rules mizname)))))

(defun translate-many (indexname)
"Translate files from index"
(save-excursion
  (find-file indexname)
  (let* ((names (split-string (buffer-string) "\n"))
	 (used (make-hash-table :size (length names) :test 'equal))
	 (mizsymbs (create-name-hash mizar-syms)))
    (while names
      (translate-file (car names) used mizsymbs)
      (setq names (cdr names))))))



