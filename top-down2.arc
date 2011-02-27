(load "lex.arc")

(= first (table)
   first!exp '(id int true false string read - ? |(|)
   first!stm (join first!exp '(if do fa break exit writes write return |;|)))

(def lookup-scope (item f scope)
  (aif no.scope nil
       (f.scope item)
       it
       (lookup-type item cdr.scope)))

(def lookup-var (var scope)
  (lookup-scope var [caar:car _] scope))

(def lookup-type (typ scope)
  (lookup-scope typ [cadr:car _] scope))

(def append (xs x)
  (join xs list.x))

(def values (xs)
  (map cadr xs))

(def chain (args . fns)
  ((afn (fns args)
         (if no.fns
               args
             (no car.fns)
               (self cdr.fns args)
             (isa car.fns 'fn)
               (self cdr.fns (apply car.fns args))
             (isa car.fns 'sym)
               (self cdr.fns (apply (expect car.fns) args))))
   fns args))

(def parse-err (f toks)
  (err (if car.toks
           (tostring:prn "Error on line " (last car.toks) ": Expected " f ", but received \"" caar.toks "\"")
           (string "Expected " f " but reached unexpected end of input\n"))))

(def expect (s)
  (fn (ast toks scope)
      (aif (is caar.toks s)
           pop.toks
           (parse-err s toks))
      (list ast toks scope)))

(def ? (sym (o exp nil))
  (fn (ast toks scope)
    (if (or (and first.sym
                 (find caar.toks first.sym))
            (is caar.toks sym))
        (if (isa exp 'fn)
            (exp ast toks scope)
            (expect.sym ast toks scope))
        (list ast toks scope))))

(def parse (s)
  (let toks lex.s
    (on-err [disp details._]
            [program nil toks (list:list (table)
                                    (obj int '(int) string '(string)))])))

(def program (ast toks scope)
  (if toks
      (let (ast toks scope)
           ((case caar.toks
              var vardef 
              type typedef 
              forward forward)
            ast toks scope)
        (program ast toks scope))
      (list ast toks scope)))

(def exp-primary (ast toks scope)
  (aif (find caar.toks first!exp)
       ((case it
          id exp-id 
          int integer 
          true true 
          false false 
          string str 
          read ice-read
          |(| (fn args (chain args '|(| exp '|)|)))
        ast toks scope)))

(def typedef (ast toks scope)
  (let ((id typ . dims) toks) (chain (list nil toks scope) 'type id '= typeid (? '|[| typearray) '|;|)
       (= (scope.0.1 id.1) (join (list:car:lookup-type typ scope)
                                 dims
                                 (cdr:lookup-type typ scope)))
       (list ast toks scope)))

(def typeid (ast toks scope)
  (let (((nil typ l)) toks scope) (id nil toks scope)
    (if (lookup-type typ scope)
        (list (append ast typ) toks scope)
        (err:string "Type " typ " is not defined on line " l "."))))

(def typearray (ast toks scope)
  (let (dim toks scope) (chain (list nil toks scope) '|[| int '|]|)
    ((if (is caar.toks '|[|)
         typearray
         list)
     (append ast dim.0.1) toks scope)))

(def vardef (ast toks scope)
  (let (ds toks scope) (chain (list nil toks scope) 'var varlist '|;|)
       (each d ds
             (let typ last.d
               (each var (rev:cdr:rev d)
                     (if acons.var
                         (= (scope.0.0 var.1) typ)))))
       (list ast toks scope)))

(def varlist (ast toks scope)
  (let (d toks scope) (chain (list nil toks scope) idlist ': vartype)
    ((if (is caar.toks '|,|)
         varlist
         list)
     (append ast d) toks scope)))

(def vartype (ast toks scope)
  (let (typ toks scope) (chain (list nil toks scope) typeid (? '|[| typearray))
       (list (append ast typ) toks scope)))

(def forward (ast toks scope)
  (let ((i parms) toks scope) (chain (list nil toks scope) 'forward id '|(| declist '|)| '|;|)
       (list i parms)))

(def declist (ast toks scope)
  ((if (is caar.toks '|)|)
       list
       declistx)
   ast toks scope))

(def declistx (ast toks scope)
  (let (d toks scope) (chain (list nil toks scope) (? '|,|) idlist ': typeid)
    ((if (is caar.toks '|,|)
         declistx
         list)
     (append ast d) toks scope)))

(def idlist (ast toks scope)
  (chain (list ast toks scope) (? '|,|) id (? '|,| idlist)))

(def id (ast toks scope)
  (if (is caar.toks 'id)
      (list (append ast pop.toks) toks scope)
      (parse-err 'id toks)))

(def int (ast toks scope)
  (if (is caar.toks 'int)
      (list (append ast pop.toks) toks scope)
      (parse-err 'int toks)))