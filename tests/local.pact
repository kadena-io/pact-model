(module j g
  (defcap g () true)
  (defun gg-mgr (i:integer r:integer)
    (let*
      ((x (- i r)))
      (enforce (>= x 0) "boom")
      (print (+ "hi from capability mgr" (format " AMOUNT:  {}   R: {}" [i, r])))
      x
      )
  )
  (defcap gg (dispatch:string amt:integer)
    @managed amt gg-mgr
    true
    )
  (defcap stateless () true)

  (defun f (person:string amt:integer)
    (with-capability (gg person amt)
      1
      (require-capability (gg person amt))
      (with-capability (stateless) 1)
      2
      )
    )
  )

(print "hi-1")
(install-capability (gg "bob" 200000))
(install-capability (gg "alice" 15000))
(print "hi-2")
(f "bob" 3)
(f "alice" 6)
(f "bob" 9)
(f "alice" 12)
(f "bob" 15)