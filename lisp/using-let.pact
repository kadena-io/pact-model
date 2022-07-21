;; Stateless capabilities could be replaced by locally defined functions using
;; `enforce` (abstracting the call to `enforce` into its own function, in case
;; it needs to be reused in multiple places). Here, the definition of the
;; local functions is explicitly scoped to (and may be inlined into) the
;; allowable call sites.

(module example2 gov

  (flet
      ((foo-cap (value:integer)
         (enforce (> value 0) "Value must be greater than zero"))

       (foo (value:integer)
         (foo-cap value)
         (print value))

       (bar-cap (value:integer)
         (enforce (< value 0) "Value must be less than zero"))

       (bar (value:integer)
         (bar-cap value)
         (print value)))

    (defun entry1 (value:integer)
      (if (> value 0)
          (foo value)
          (if (< value 0)
              (bar value)
              (print "entry ignoring a zero value"))))

    (defun entry2 (value:integer)
      (if (> value 0)
          (foo value)
          (if (< value 0)
              (bar value)
              (print "entry ignoring a zero value"))))))

;; Stateful capabilities are just capabilities paired with the idea of a
;; diminishing resource.

(module example3 gov

  (defvar resource-table (make-hash-table))

  (flet
      ((foo-mgr (current:integer requested:integer)
         (enforce (<= requested current))
         (- current requested))

       (foo-cap (value:integer requested:integer)
         (enforce (> value 0) "Value must be greater than zero")
         (update-resource-if resource-table 'foo #'foo-mgr requested))

       (foo (value:integer)
         (foo-cap value 1)
         (print value))

       (bar-cap (value:integer)
         (enforce (< value 0) "Value must be less than zero"))

       (bar (value:integer)
         (bar-cap value)
         (print value)))

    (defun entry1 (value:integer)
      (if (> value 0)
          (foo value)
          (if (< value 0)
              (bar value)
              (print "entry ignoring a zero value"))))

    (defun entry2 (value:integer)
      (if (> value 0)
          (foo value)
          (if (< value 0)
              (bar value)
              (print "entry ignoring a zero value"))))))

(install-resource resource-table 'foo 10)
