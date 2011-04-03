(= reg* 0 ;current register offset
   base* 7 ;registers less than 8 are reserved
   ice-fns* (table) ;table of fns for ast
   zero* 0 ;register 0 always contains 0
   one* 1 ;register 1 is always 1
   two* 2 ;register 2 is always 2
   acc* 3 ;the accumulator
   pc* 7 ;register 7 is the program counter
   sp* 6 ;register 6 is the stack pointer
   fp* 5 ;register 5 is the data pointer
   data* nil ;list of data items
   data-size* 1 ;next available offset in memory 
   type* 'int) ;type of current expression

(def nextreg _
  (+ (++ reg*) base*))

(def clear-reg nil
  (= reg* 0))

(mac w/reg (reg . body )
  `(let ,reg ,(if (acons reg) 
                  `(list ,@(n-of len.reg '(nextreg)))
                  '(nextreg))
     ,@body))

(def DATA (d (o s len.d))
  (zap [append _ d] data*)
  (let tmp data-size*
    (++ data-size* s)
    tmp))

(def SDATA (s)
  (let tmp data-size*
    (DATA len.s)
    (DATA (string #\" s #\") len.s)
    tmp))

;Instructions
(mac definst (name args doc)
     `(def ,name ,args ,doc
        (prn ',name " " ,@(intersperse ", " args))
        ,car.args))

(onmac definst
  (HALT nil    "stop execution")
  (IN (r)      "reg[r] <- input integer value of register r from stdin")
  (OUT (r)     "reg[r] -> output integer value of register r to stdout")
  (INB (r)     "reg[r] <- input boolean value of register r from stdin")
  (OUTB (r)    "reg[r] -> output boolean value of register r to stdout")
  (OUTC (r)    "reg[r] -> output ASCII character of register r to stdout")
  (OUTNL nil   "output a newline to stdout")
  (ADD (r s t) "reg[r] = reg[s] + reg[t]")
  (SUB (r s t) "reg[r] = reg[s] - reg[t]")
  (MUL (r s t) "reg[r] = reg[s] * reg[t]")
  (DIV (r s t) "reg[r] = reg[s] / reg[t]"))

(mac defreg->mem (name doc)
     `(def ,name (r (o d 0) (o s 0)) ,doc
        (prn ',name " " r ", " d "(" s ")")))

(onmac defreg->mem
  (LDC "reg[r] = d (immediate; x ignored)")
  (LDA "reg[r] = d + reg[s] (direct)")
  (LD "reg[r] = dMem[d + reg[s]] (indirect)")
  (ST "dMem[d + reg[s]] = reg[r]")
  (JLT "if reg[r]<0 reg[PC] = d + reg[s]")
  (JLE "if reg[r]<=0 reg[PC] = d + reg[s]")
  (JEQ "if reg[r]==0 reg[PC] = d + reg[s]")
  (JNE "if reg[r]!=0 reg[PC] = d + reg[s]")
  (JGE "if reg[r]>=0 reg[PC] = d + reg[s]")
  (JGT "if reg[r]>0 reg[PC] = d + reg[s]"))

(def PUSH (r)
  (ST r 1 sp*)
  (LDA sp* 1 sp*))

(def POP (r)
  (LD r 0 sp*)
  (LDA sp* -1 sp*))

(def GOTO (d (o r 7))
  (LDA 7 d r))

(def INCR (r)
  (LDA r 1 r))

(def DECR (r)
  (LDA r -1 r))

(def ice-eval (x)
  (aif (atom x) x
       (ice-fns* car.x) (apply it cdr.x)))

(mac defice (name args . body)
     `(= (ice-fns* ',name)
         (fn ,args ,@body)))

(mac defconst (name args val (o typ name))
  (w/uniq r
    `(defice ,name ,args
       (= type* ',typ) ;type of an expression is determined by its leaves
       (w/reg ,r
            (LDC ,r ,val)
            ,r))))

(mapmac defconst
  ((int (i) i)
   (string (s) (SDATA s))
   (true nil 1 bool)
   (false nil 0 bool)))

(defice exit nil
  (HALT))

(mac iceop (name registers . body)
  (w/uniq args
    `(defice ,name ,args
       (let ,registers (map ice-eval ,args)
            ,@body))))

(mac binop (name inst)
  (w/uniq (a b)
    `(iceop ,name (,a ,b)
       (,inst (nextreg) ,a ,b))))

(binop * MUL)
(binop / DIV)

(iceop + (a b)
  (w/reg r 
    (ADD r a b)
    (if (is type* 'bool)
        (DIV r r 2))))

(iceop - (a b)
  (w/reg r
    (if b
        (SUB r a b)                     ;binary
        (if (is type* 'int)             ;unary
            (SUB r zero* a)             ;int
            (SUB r one* a)))))          ;bool

(iceop ? (a)
  (= type* 'int)
  a)

(iceop % (a b)
  (w/reg r
    (DIV r a b)
    (MUL r r b)
    (SUB r a r)
    r))

(mac icecomp (name inst)
  (w/uniq (r a b)
    `(iceop ,name (,a ,b)
       (w/reg ,r
         (SUB ,r ,a ,b)
         (,inst ,r 2 pc*)
         (LDC ,r 0)
         (GOTO 1)
         (LDC ,r 1)))))

(onmac icecomp
  (= JEQ)
  (!= JNE)
  (< JLT)
  (> JGT)
  (<= JLE)
  (>= JGE))

(iceop := (place val)
  (ST val place zero*))

(iceop write (a)
  (if (is type* 'bool)
      (OUTB a)
      (OUT a)))

(iceop writes (a)
  (w/reg (l r)
    (LD l 0 a)                          ;load length into l
    (LD r 1 a)                          ;load next character into r
    (OUTC r)                            ;output character
    (DECR l)                            ;decrememnt length
    (INCR a)                            ;incrememnt address
    (JGT l -4 pc*)                      ;loop until finished
    (OUTNL)))

(iceop read nil
  (w/reg r
    (IN r)
    r))

(defice if forms
  (let clauses pair.forms
    (each x clauses
      (with (cond (tostring:ice-eval: x.0)
             then (tostring:ice-eval: x.1))
        ))))

(def ice-cap (form)
  (w/outstring out
    (w/stdout out
      (let r (ice-eval form)
        (list r inside.out)))))

(defice do (test body)
  (withs ((tr test) (ice-cap test)
          (br body) (ice-cap body)
          tl (len lines.test)
          bl (len lines.body))
    pr.test
    (JEQ tr (+ bl 1) pc*)
    pr.body
    (GOTO (- 0 bl tl))))

(def compile (s)
  (= data* nil
     data-size* 1
     reg* 0
     line* 0)
  (w/lines lines (map ice-eval (car:parse s))
     (each x data*
        (if (isa x 'string)
            (prn ".SDATA " x)
            (prn ".DATA " x)))
     (zap [append _ (tostring:HALT)] lines)
     (forlen i lines (prn i  ":\t" lines.i))))