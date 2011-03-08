(load "lex.arc")
(load "utilities.arc")

(= first (table)
   first!exp '(id int true false string read - ? |(|)
   first!stm (join first!exp '(if do fa break exit writes write return |;|))
   exp-toks (join first!exp '(+ - * / % = != > < >= <= |,| |)|))
   ops* (table)
   default-scope (list:list (table)
                            (obj int '(int) string '(string) bool '(bool))
                            (table)))

(implicit in-loop)

(def parse (s)
  (= forwards* (table))
  (let toks lex.s
    (on-err [prn details._]
            [program nil toks create-scope.default-scope])))

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
            (with (ti (exp-type i scope toks)
                   tv (exp-type v scope toks))
              (if (~iso ti tv)
                  (compile-err toks "Invalid type in assignment to " i.1 ": " tv)
                  (is in-loop i.1)
                  (compile-err toks "Invalid assignment to loop variable: " i.1)))
            (list (append ast (list 'assign i v)) toks scope))))

(mac defnode (name body (o sym name) (o loop))
     `(def ,name (ast toks scope)
        ,([if loop
              `(w/param in-loop t ,_)
              _]             
          `(let (x toks scope) (chain (list nil toks scope) ,@body)
                (list (append ast (cons ',sym x)) toks scope)))))

(defnode write-exp
  ('write exp (T '(int) '(string)) '|;|)
  write)

(defnode writes
  ('writes exp (T '(int) '(string)) '|;|))

(defnode exit
  ('exit '|;|))

(defnode return
  ('return '|;|))

(defnode if-exp
  ('if exp (T '(bool)) '-> stms (? '|[]| if-rest) 'fi)
  if)

(def if-rest (ast toks scope)
  (chain (list ast toks scope)
         '|[]|
         (? 'else 'else (list exp (T '(bool)))) 
         '-> stms (? '|[]| if-rest)))

(defnode do-exp
  ('do exp (T '(bool)) '-> stms 'od)
  do
  t)

(def break (ast toks scope)
  (if in-loop
      (let (x toks scope) (chain (list nil toks scope) 'break '|;|)
           (list (append ast (cons 'break x)) toks scope))
      (compile-err toks "Break is only permitted inside a loop")))


(def fa (ast toks scope)
  (let (((nil i) start end) toks scope) (chain (list nil toks scope) 'fa id ':= exp (T '(int)) 'to exp (T '(int)) '->)
       (let scope create-scope.scope
         (= (scope.0.0 i) '(int))
         (w/param in-loop i
           (let (body toks scope) (chain (list nil toks scope) stms 'af)
                (list (append ast (list 'fa i start end body)) toks cdr.scope))))))

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

(def exp-unary (ast toks scope)
  (let (x toks scope) 
    (aif (find caar.toks '(- ?))
         (exp-unary list.it cdr.toks scope)
         (exp-primary nil toks scope))
    (list ((if (find car.x '(- ?)) append join) ast x) toks scope)))

(mac exp-helper (name symbols next)
     `(def ,name (ast toks scope)
        (let (x toks scope) (,next nil toks scope)
             (= ast (append but-last.ast ((if last.ast append join) last.ast car.x)))
             (aif (find caar.toks ',symbols)
                  (,name (append but-last.ast (list it last.ast)) cdr.toks scope)
                  (list ast toks scope)))))

(exp-helper exp-term (* / %) exp-unary)

(exp-helper exp-factor (+ -) exp-term)

(exp-helper exp-main (= != > < >= <=) exp-factor)

(def exp (ast toks scope)
  (let ((x) toks scope) (exp-main nil toks scope)
    (let typ (exp-type x scope toks)
      (list (append ast x) toks scope typ))))

(mac op (names . types)
     (each n ([if acons._ _ list._] names)
           (map (fn (typ) 
                    (zap [cons (maptree list typ) _] 
                         ops*.n))
                pair.types)))

(op - 
    (int) int
    (bool) bool)
(op ?
    (bool) int)
(op (- /)
    (int int) int)
(op (+ *)
    (int int) int
    (bool bool) bool)
(op (= !=)
    (int int) bool
    (bool bool) bool)
(op (> < >= <=)
    (int int) bool)

(def check-op (x scope toks)
  (withs (types ([aif ops*._ it
                      (compile-err toks "Op not defined: " _)]
                 car.x)
          tps (map [exp-type _ scope toks]
                   cdr.x))
    (aif (find tps (map car types))
         (alref types it)
         (compile-err toks "Incorrect argument types for op " car.x ": " tps))))

(def exp-type (x scope toks)
  (case car.x
    int '(int)
    string '(string)
    true '(bool)
    false '(bool)
    read '(int)
    ((case car.x
       var var 
       call call
       check-op)
     x scope toks)))

(def call (x scope toks)
  (aif (lookup-proc x.1 scope)
       (let types (map [exp-type _ scope toks] cddr.x)
         (if (iso types (map cadr cdr.it))
             (list car.it)
             (compile-err toks "Incorrect arguments in call to " x.1 ": " cddr.x)))
       (compile-err toks "Undefined procedure: " x.1)))

(def var (x scope toks)
  (aif (lookup-var x.1 scope)
       (let typ (join (list car.it) (nthcdr (len cdr.x) it))
         (if (> (len cddr.x) (len cdr.it))
             (compile-err toks "Too many dimensions for variable " x.1 ": " (len cddr.x))
             typ))
       (compile-err toks "Undefined variable: " x.1)))

(def exp-call (ast toks scope)
  (withs ((i toks scope) (id ast toks scope)
          p i.0.1)
       (aif (lookup-proc p scope)
            (let (x toks scope) (chain (list (list 'call p) toks scope) '|(| (? 'exp exp-list) '|)|)
                 (list (append ast x) toks scope))
            (compile-err toks "Undefined procedure: " p))))

(def exp-list (ast toks scope)
  (chain (list ast toks scope) (? '|,|) exp (? '|,| exp-list)))

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
        (compile-err toks "Type " typ " is not defined on line " l "."))))

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
               (each var but-last.d
                     (if acons.var
                         (if (scope.0.0 var.1)
                             (compile-err toks "Duplicate declaration: " var.1)
                             (= (scope.0.0 var.1) typ))))))
       (list ast toks scope)))

(def varlist (ast toks scope)
  (let (d toks scope) (chain (list nil toks scope) idlist ': vartype)
    ((if (is caar.toks '|,|)
         varlist
         list)
     (append ast d) toks scope)))

(def vartype (ast toks scope)
  (let ((n . ds) toks scope) (chain (list nil toks scope) typeid (? '|[| typearray))
       (let tp (lookup-type n scope)
         (list (append ast (join (list car.tp) ds cdr.tp)) toks scope))))

(def get-parms (xs scope)
  (let parms (apply join (map (fn (xs)
                                  (map (fn (x)
                                           (list x (lookup-type last.xs scope)))
                                       (values:but-last xs)))
                              xs))
    (aif (dups (map car parms))
         (err:string "line " name.2 ": Duplicate procedure variable: " car.it))
    parms))

(def defproc (name parms typ scope)
  (let parms (get-parms parms scope)
    (= (scope.0.2 name)
       (cons typ parms))
    (let scope create-scope.scope
      (each p ([if typ
                   (cons (list name list.typ) _)
                   _]
               parms)
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
            (list (append ast (but-last pop.toks)) toks scope)
            (parse-err ',typ toks))))

(terminal id)
(terminal integer int)
(terminal str string)
(terminal true)
(terminal false)
(terminal ice-read read)
