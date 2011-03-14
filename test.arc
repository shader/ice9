#! /bin/bash
#|
arc_dir="./ar";

exec $rl ./racket/bin/racket --no-init-file --repl --load "$0" ${1+"$@"}
|#
(current-directory "./ar")
(require "ar/ac.scm" "ar/brackets.scm")
(use-bracket-readtable)
(aload "arc.arc")
(aload "libs.arc")
(current-directory "..")
(aload "lex.arc")
(aload "utilities.arc")
(aload "parse.arc")

(arc-eval '(= failures nil
              log "./test.log"))

(arc-eval '(w/outstring out 
              (each f (dir "tests")
                    (pr f "... ")
                    (withs (in infile.f
                            l  readline.in
                            (nil e num c) (re-match "#(error|compile|unknown) ([0-9]+)(?:, (.*))*" l)
                            c (split ))
                      (on-err [if (findsubseq "error" l)
                                  (pr "Successful error: " details._)
                                  (do (pr "Failure: compile error expected: " l)
                                      (push failures f))]
                              [parse infile.f])))
              (write failures outfile.log)
              (disp out outfile.log)
              (disp out)))