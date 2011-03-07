(def append (xs x)
  (join xs list.x))

(mac erp (x)
  (w/uniq (gx)
    `(let ,gx ,x
       (w/stdout (stderr)
         (pr ',x ": ") (write ,gx) (prn))
       ,gx)))

(mac implicit (name (o val))
  `(defvar ,name ($.make-parameter ,val)))

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

(def but-last (xs)
  (rev:cdr:rev xs))
