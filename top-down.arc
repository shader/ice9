(load "lex.arc")

(= toks nil
   nodes (table)
   first (table)
   first!exp '(id int true false string read - ? |(|)
   first!stm (join first!exp '(if do fa break exit return |;|)))

(mac defnode (name args . body)
     `(= (nodes ',name)
	 (fn ,args
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
                                         expect.it)
                                     (expect car.l))))
             (self cdr.l acc)))
   l nil))

(def parse (s)
  (= toks lex.s)
  (on-err [disp details._]
          [expect 'program]))

(defnode program ()
  `(program
    ,(expect 'typedef)))

(defnode stms ()
  (expects 'stm 
           [? 'stm 'stms]))

(defnode stm ()
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

(defnode typedef ()
  `(typedef
    ,@(expects 'type 'id '= 'typeid 
               [? '|[| 'typearray]
               '|;|)))

(defnode typeid ()
  expect!id)

(defnode typearray ()
  (expects '|[| 'int '|]| 
           [? '|[| 'typearray]))

(defnode idlist ()
  (expects 'id [? '|,| 'idrest]))

(defnode idrest ()
  (expects '|,| 'id
           [? '|,| 'idrest]))

(defnode vardef ()
  `(vardef ,@(expects 'var 'varlist '|;|)))

(defnode varlist ()
   (expects 'idlist ': 'typeid
            [? '|[| 'typearray] 
            [? 'id 'varlist]))

(defnode declist ()
  `(declist ,@(expects 'idlist '|:| 'typeid)
            ,@(if (is (next) '|,|)
                  (expects '|,| 'declist))))