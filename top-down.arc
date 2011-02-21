(load "lex.arc")

(= toks nil
   nodes (table)
   first (table)
   first!exp '(id int true false string read - ? |(|)
   first!stm (join first!exp '(if do fa break exit writes write return |;|)))

(mac defnode (name . body)
     `(= (nodes ',name)
	 (fn nil
	     ,@body)))

(def parse-err (f)
  (err (if car.toks
           (tostring:prn "Error on line " (last car.toks) ": Expected " f ", but received \"" caar.toks "\"")
           (string "Expected " f " but reached unexpected end of input\n"))))

(def expect (f)
  (aif (aand nodes.f (it))
         it
       (is caar.toks f)
         (list pop.toks)
       parse-err.f))

(def ? (sym exp)
  (if (or (and first.sym
               (find (next) first.sym))
          (is (next) sym))
      (if (isa exp 'fn)
          (exp)
          exp)))

(def next () caar.toks)

(def expects l
  ((afn (l acc)
         (if no.l
               acc
             car.l
               (self cdr.l (join acc
                                 (if (isa car.l 'fn) 
                                       (aif (car.l)
                                            (if acons.it 
                                                expects.it
                                                expect.it))
                                     (acons car.l)
                                       (apply expects car.l)
                                     (expect car.l))))
             (self cdr.l acc)))
   l nil))

(def chain (args . fns)
  ((afn (fns args)
         (if fns
             (self cdr.fns (apply car.fns args))
             args))
   fns args))

(def parse (s)
  (= toks lex.s)
  (on-err [disp details._]
          [expect 'program]))

(defnode program
  `(program
    ,(expect 'typedef)))

(defnode stms
  (expects 'stm 
           [? 'stm 'stms]))

(defnode stm
  (if (find (next) first!stm)
      `((stm
         ,@(case (next)
             if expect!if
             do expect!do
             fa expect!fa
             write (expects 'write 'exp '|;|)
             writes (expects 'writes 'exp '|;|)
             break (expects 'break '|;|)
             exit (expects 'exit '|;|)
             return (expects 'return '|;|)    
             |;| (expects '|;|))))
      parse-err!stm))

(defnode exp-primary
  (if (find (next) first!stm)
      (case (next)
        id expect!exp-id
        int expect!int
        true expect!true
        false expect!false
        string expect!string
        read expect!read
        |(| (expects '|(| 'exp  '|)| ))))

(defnode exp-id
  (aif cdr.toks
      (case caar.it
        |[| expect!lvalue
        |(| expect!exp-call
        expect!lvalue)
      expect!lvalue))

(defnode unary-op
  (expects [find (next) '(- ?)]
           [? '- 'unary-op]
           [? '? 'unary-op]))

(defnode exp-unary
  (list:expects [find (next) '(- ?)]
                [? '- 'exp-unary] [? '? 'exp-unary] 'exp-primary))

(defnode exp-term
  (list:expects 'exp-unary [aif (find (next) '(* / %))
                                (list it 'exp-term)]))

(defnode exp-factor
  (list:expects 'exp-term [aif (find (next) '(+ -))
                               (list it 'exp-factor)]))

(defnode exp
  (list:expects 'exp-factor [if (find (next) '(= != > < >= <=))
                                (list it 'exp)]))

(defnode exp-call
  (expects 'id '|(| [if (find (next) first!exp)
                        exp-list]
               '|)|))

(defnode exp-list
  (expects exp [if (is (next) '|,|)
                   '(|,| exp-list)]))

(defnode typedef
  `(typedef
    ,@(expects 'type 'id '= 'typeid 
               [? '|[| 'typearray]
               '|;|)))

(defnode typeid
  expect!id)

(defnode typearray
  (expects '|[| 'int '|]| 
           [? '|[| 'typearray]))

(defnode idlist
  (expects 'id [? '|,| 'idrest]))

(defnode idrest
  (expects '|,| 'id
           [? '|,| 'idrest]))

(defnode vardef
  `(vardef ,@(expects 'var 'varlist '|;|)))

(defnode varlist
   (expects 'idlist ': 'typeid
            [? '|[| 'typearray] 
            [? 'id 'varlist]))

(defnode declist
  (join list!declist expect!declist-main))

(defnode declist-main
  (join (expects 'idlist '|:| 'typeid)
        (if (is (next) '|,|)
            (expects '|,| 'declist-main))))

(defnode lvalue
  (expects 'id [? '|[| 'lvalue-rest]))

(defnode lvalue-rest
  (expects '|[| 'exp '|]| [? '|[| 'lvalue-rest]))