(= literal '(if fi else do od fa af to proc end return forward var type break exit true false write writes read
             |[]|
             ->
             |(|
             |)|
             |[|
             |]|
             :=
             :
             |;|
             ?
             |,|
             +
             -
             *
             /
             ^
             >=
             <=
             !=
             =
             >
             <
             %)

   special `(id        "^[A-Za-z][A-Za-z0-9_]*"  ,[sym _]
             int       "^[0-9]+"                 ,[coerce _ 'int]
             string    "^\"[^\"\n]*\"|'[^'\n]*'" ,idfn
             comment   "^\\#.*"                  nil
             space     "^[ \t]+"                 nil))

(def get-tok (s)
  (point return
    (each r literal
          (if (headmatch string.r s)
              (return list.r)))
    (each sp (tuples special 3)
	  (aif (re-match sp.1 s)
	       (if (isa sp.2 'fn)
		   (return (list car.sp (sp.2 car.it)))
		   (return (len car.it)))))))

(def get-toks (s)
  ((afn (s (o acc nil))
     (if empty.s acc
	 (let tok (get-tok s)
	   (if no.tok (err:string "illegal character (" s.0 ")")
	       (isa tok 'int) (self (cut s tok) acc)
               (self (cut s (aif cadr.tok
                                 (len string.it)
                                 (len:string:car tok)))
                     (join acc list.tok))))))
   s))

(def lex (s)
  (if (isa s 'string) (= s instring.s))
  ((afn (l i acc)
        (if l
            (on-err [do (prn "line " i ": " details._) quit.1]
                    (fn () (self readline.s ++.i (join acc (map [join _ list.i] (get-toks l))))))
            acc))
   readline.s 0 nil))