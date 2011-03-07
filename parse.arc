(load "lex.arc")
(load "utilities.arc")

(= first (table)
   first!exp '(id int true false string read - ? |(|)
   first!stm (join first!exp '(if do fa break exit writes write return |;|))
   exp-toks (join first!exp '(+ - * / % = != > < >= <= |,| |)|))
   binops* (table)
   unops* (table))

(implicit in-loop)

(def lookup-scope (item f scope)
  (aif no.scope nil
       (f.scope item)
       it
       (lookup-scope item f cdr.scope)))

(def lookup-var (var scope)
  (lookup-scope var [_.0 0] scope))

(def lookup-type (typ scope)
  (lookup-scope typ [_.0 1] scope))

(def lookup-proc (proc scope)
  (lookup-scope proc [_.0 2] scope))

(def create-scope (scope (o vars (table)) (o types (table)) (o procs (table)))
  (cons (list vars types procs)
        scope))

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
           (string "Expected " f " but reached unexpected end of input."))))

(def expect (s)
  (fn (ast toks scope)
      (aif (is caar.toks s)
           pop.toks
           (parse-err s toks))
      (list ast toks scope)))

(def ? (sym (o exp sym) (o else list))
  (fn (ast toks scope)
      (([if (isa _ 'fn)
            _
            expect._]
        (if (or (and first.sym
                     (find caar.toks first.sym))
                (is caar.toks sym))
            exp
            else))
       ast toks scope)))

(def T (typ)
  (fn (ast toks scope tp)
      (if (iso tp typ)
          (list ast toks typ scope)
          (err:string "Expected expression of type " typ " but received " tp))))

(def parse (s)
  (let toks lex.s
    (on-err [prn details._]
            [program nil toks (list:list (table)
                                         (obj int '(int) string '(string) bool '(bool))
                                         (table))])))

(def program (ast toks scope)
  (if toks
      (if (find caar.toks first!stm)
          (stms ast toks scope)
          (let (ast toks scope)
            ((case caar.toks
               var vardef 
               type typedef 
               forward forward
               proc proc)
             ast toks scope)
            (program ast toks scope)))
      (list ast toks scope)))

(def stms (ast toks scope)
   (chain (list ast toks scope) stm (? 'stm stms)))

(def stm (ast toks scope)
  (aif (is caar.toks 'id)
       (stm-id ast toks scope)
       (find caar.toks first!exp)
       (chain (list ast toks scope) exp '|;|)
       (find caar.toks first!stm)
       ((case it
          if if-exp
          do do-exp
          fa fa
          write write-exp
          writes writes
          break break
          exit exit
          return return
          |;| (fn args (chain args '|;|)))
        ast toks scope)
       (parse-err 'statement toks)))

(def stm-id (ast toks scope)
  (let (x (next . rest) scope) (lvalue ast toks scope)
       (chain (list ast toks scope)
              (if (is car.next ':=)
                  assignment
                  exp)
              '|;|)))

(def assignment (ast toks scope)
  (let (x toks scope) (chain (list nil toks scope) lvalue ':= exp)
       (let (i v) x
            (list (append ast (list 'assign i v)) toks scope))))

(mac defnode (name body (o sym name) (o loop))
     `(def ,name (ast toks scope)
        ,([if loop
              `(w/param in-loop t ,_)
              _]             
          `(let (x toks scope) (chain (list nil toks scope) ,@body)
                (list (append ast (cons ',sym x)) toks scope)))))

(defnode write-exp
  ('write exp '|;|)
  write)

(defnode writes
  ('writes exp '|;|))

(defnode exit
  ('exit '|;|))

(defnode return
  ('return '|;|))

(defnode if-exp
  ('if exp '-> stms (? '|[]| if-rest) 'fi)
  if)

(defnode do-exp
  ('do exp '-> stms 'od)
  do
  t)

(def break (ast toks scope)
  (if in-loop
      (let (x toks scope) (chain (list nil toks scope) 'break '|;|)
           (list (append ast (cons 'break x)) toks scope))
      (err:string "break is only permitted inside a loop")))


(def fa (ast toks scope)
  (w/param in-loop t
    (let (((nil i) start end) toks scope) (chain (list nil toks scope) 'fa id ':= exp 'to exp '->)
         (let scope create-scope.scope
           (= (scope.0.0 i) '(int))
           (let (body toks scope) (chain (list nil toks scope) stms 'af)
                (list (append ast (list 'fa i start end body)) toks cdr.scope))))))


(def if-rest (ast toks scope)
  (chain (list ast toks scope) '|[]| (? 'else 'else exp) '-> stms (? '|[]| if-rest)))

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
        ast toks scope)
       (parse-err 'expression toks)))

(def exp-id (ast toks scope)
  (aif cdr.toks
       ((case caar.it
           |[| lvalue
           |(| exp-call
           lvalue)
        ast toks scope)
       (lvalue ast toks scope)))

(def lvalue (ast toks scope)
  (let ((v . dims) toks scop) (chain (list nil toks scope) id (? '|[| lvalue-rest))
       (list (list:join (list 'var v.1) dims) toks scope)))

(def lvalue-rest (ast toks scope)
  (chain (list ast toks scope) '|[| exp '|]| (? '|[| lvalue-rest)))

(def check-var (v dims scope)
  (aif (lookup-var v.1 scope)
       (if (> len.dims (- len.it 1))
           (err:string "Invalid dimension for variable " v.1))
       (err:string "Undeclared variable " v.1)))

(def exp-unary (ast toks scope)
  (let (x toks scope) 
    (aif (find caar.toks '(- ?))
         (exp-unary list.it cdr.toks scope)
         (exp-primary nil toks scope))
    (list ((if (find car.x '(- ?)) append join) ast x) toks scope)))

(mac exp-helper (name symbols next)
     `(def ,name (ast toks scope)
          (aif (find caar.toks ',symbols)
                (,name (append (rev:cdr:rev ast) (list it last.ast)) cdr.toks scope)
                (let (x toks scope) (,next nil toks scope)
                     (= ast (append (rev:cdr:rev ast) ((if last.ast append join) last.ast car.x)))
                     (if (find caar.toks ',symbols)
                         (,name ast toks scope)
                         (list ast toks scope))))))

(exp-helper exp-term (* / %) exp-unary)

(exp-helper exp-factor (+ -) exp-term)

(exp-helper exp-main (= != > < >= <=) exp-factor)

(def exp (ast toks scope)
  (exp-main (append ast nil) toks scope))

(def exp-call (ast toks scope)
  (withs ((i toks scope) (id ast toks scope)
          p i.0.1)
       (aif (lookup-proc p scope)
            (let (x toks scope) (chain (list (list:list 'call (list p it)) toks scope) '|(| (? 'exp exp-list) '|)|)
                 (list (join ast x) toks scope))
            (err:string "Undefined procedure: " p))))

(def exp-list (ast toks scope)
  (chain (list ast toks scope) (? '|,| '|,|) exp (? '|,| exp-list)))

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
  (let (dim toks scope) (chain (list nil toks scope) '|[| integer '|]|)
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
                         (if (scope.0.0 var.1)
                             (err:string "Duplicate declaration: " var.1)
                             (= (scope.0.0 var.1) typ))))))
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

(def get-parms (xs scope)
  (let parms (apply join (map (fn (xs)
                                  (map (fn (x)
                                           (list x (lookup-type last.xs scope)))
                                       (values:rev:cdr:rev xs)))
                              xs))
    (aif (dups (map car parms))
         (err:string "line " name.2 ": Duplicate procedure variable: " car.it))
    parms))

(def defproc (name parms typ scope)
  (let parms ([if typ 
                  (cons (list name list.typ) _)
                  _]
              (get-parms parms scope))
       (= (scope.0.2 name)
          (cons typ parms))
       (let scope create-scope.scope
         (each p parms
               (= (scope.0.0 p.0) p.1))
         scope)))

(def declist (ast toks scope)
  (let (d toks nil)
    ((if (is caar.toks '|)|)
         list
         declistx)
     nil toks scope)
    (list (append ast d) toks scope)))

(def declistx (ast toks scope)
  (let (d toks scope) (chain (list nil toks scope) (? '|,|) idlist ': typeid)
    ((if (is caar.toks '|,|)
         declistx
         list)
     (append ast d) toks scope)))

(def forward (ast toks scope)
  (let (((nil i) parms typ) toks scope) (chain (list nil toks scope) 'forward id '|(| declist '|)| proctype '|;|)
       (list ast toks (cdr:defproc i parms typ scope))))

(def proc (ast toks scope)
  (withs ((((nil i) plist typ) toks scope)
            (chain (list nil toks scope) 'proc id '|(| declist '|)| proctype)
          parms (get-parms plist scope)
          (body toks scope)
            (chain (list nil toks (defproc i plist typ scope)) procbody 'end))
    (list (append ast (list 'proc i typ parms body)) toks cdr.scope)))

(def proctype (ast toks scope)
  (if (is caar.toks ':)
      (chain (list ast toks scope) ': typeid)
      (list (append ast nil) toks scope)))

(def procbody (ast toks scope)
  (if (find caar.toks first!stm)
      (stms ast toks scope)
      (is caar.toks 'end)
      (list ast toks scope)
      (let (ast toks scope)
        ((case caar.toks
           var vardef
           type typedef)
         ast toks scope)
        (procbody ast toks scope))))

(def idlist (ast toks scope)
  (chain (list ast toks scope) (? '|,|) id (? '|,| idlist)))

(mac terminal (name (o typ name))
     `(def ,name (ast toks scope)
        (if (is caar.toks ',typ)
            (list (append ast (rev:cdr:rev pop.toks)) toks scope)
            (parse-err ',typ toks))))

(terminal id)
(terminal integer int)
(terminal str string)
(terminal true)
(terminal false)