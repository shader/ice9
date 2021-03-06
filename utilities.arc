(def listify (x)
  (if (or no.x acons.x)
      x
      list.x))

(def append (xs x)
  (join xs list.x))

(mac append-ast (x)
     `(list (append ast ,x) toks scope))

(mac erp (x)
  (w/uniq (gx)
    `(let ,gx ,x
       (w/stdout (stderr)
         (pr ',x ": ") (write ,gx) (prn))
       ,gx)))

(mac implicit (name (o val))
  `(defvar ,name ($.make-parameter ,val)))

(mac mapmac (m l)
     (eval ``(do ,@(map [apply (rep ,m) _] ',l))))

(mac onmac (m . l)
  `(mapmac ,m ,l))

(mac w/param (name val . body)
     (w/uniq (param f v) 
       `(with (,f (fn () ,@body)
               ,param (defvar-impl ,name)
               ,v ,val)
          ($ (parameterize ((,param ,v)) (,f))))))

(def dups (xs)
  ((afn ((x . xs) acc)
        (if no.x rev.acc
            (do (and (find x xs) (no:find x acc)
                     (push x acc))
                (self xs acc))))
   xs nil))

(def maptree (f tree)
  (if no.tree nil
      atom.tree f.tree
      (cons (maptree f car.tree)
            (maptree f cdr.tree))))

(def expect (s)
  (fn (ast toks scope . typ)
      (aif (is caar.toks s)
           pop.toks
           (parse-err s toks))
      (list ast toks scope)))

(def ? (sym (o exp sym) (o else list))
  (fn (ast toks scope . typ)
      (([if (isa _ 'fn)
            _
            acons._
            (fn args
                (apply chain args _))
            expect._]
        (if (or (and first.sym
                     (find caar.toks first.sym))
                (is caar.toks sym))
            exp
            else))
       ast toks scope)))

(def T types
  (fn (ast toks scope tp)
      (if (find tp types)
          (list ast toks scope)
          (compile-err toks "Expected expression of type " types " but received " tp))))

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
               (self cdr.fns (apply (expect car.fns) args))
             (acons car.fns)
               (self cdr.fns (apply chain args car.fns))))
   fns args))

(def compile-err (toks . m)
  (with (l (if car.toks 
               (last car.toks)
               last-line)
         m (apply tostring:pr m))
    (err (tostring:prn "line " l ": " m))))

(def parse-err (f toks)
  (compile-err
   toks
   ([string "Expected " f " but received " _ " instead."]
    (aif car.toks
         car.it
         "end of file"))))

(mac w/lines (x form . body)
  (w/uniq gv
    `(let ,gv (instring:tostring ,form)
       (let ,x (drain (readline ,gv))
            ,@body))))