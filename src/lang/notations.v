From stdpp Require Import base.
From stdpp Require Export binders.
From intdet.lang Require Export syntax.

(* From https://plv.mpi-sws.org/coqdoc/iris/iris.bi.weakestpre.hexprl *)
Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.

Declare Scope val_scope.
Delimit Scope val_scope with V.
Bind Scope val_scope with val.

(* ------------------------------------------------------------------------ *)

(* Notations for values. *)

(* These notations can produce ASTs of type [val] and [expr], and are active
   in the scopes [%V] and [%T]. *)

(* [#l] denotes the memory location [l], viewed as a value. *)

Notation "# l" :=
  (VLoc l%V%stdpp)
  (at level 8, format "# l")
: val_scope.

(* [^ n] denotes the integer [n], as a value, and an expr. *)

Notation "^ n" :=
  (VInt n)%Z
  (at level 8, format "^ n")
  : val_scope.

(* [λ: xs, i] denotes the function whose formal parameters are [_::xs]
   and whose body is [i]. The formal parameters must be expressed as a
   tuple, delimited with double square brackets. *)

Notation "'μ:' f x y .. z , e" := (Code f%binder x%binder (Code BAnon y%binder .. (Code BAnon z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
  format "'[' 'μ:' f x y .. z , '/ ' e ']'") : expr_scope.

Notation "'μ:' f x y .. z , e" := (VCode f%binder x%binder (Code BAnon y%binder .. (Code BAnon z%binder e%E) ..))
  (at level 200, f, x, y, z at level 1, e at level 200,
     format "'[' 'μ:' f x y .. z , '/ ' e ']'") : val_scope.

Notation "λ: x , e" := (Code BAnon x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:' x , '/ ' e ']'") : expr_scope.
Notation "λ: x y .. z , e" := (Code BAnon x%binder (Code BAnon y%binder .. (Code BAnon z%binder e%E) ..))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:' x y .. z , '/ ' e ']'") : expr_scope.

Notation "λ: x , e" := (VCode BAnon x%binder e%E)
  (at level 200, x at level 1, e at level 200,
   format "'[' 'λ:' x , '/ ' e ']'") : val_scope.
Notation "λ: x y .. z , e" := (VCode BAnon x%binder (Code BAnon y%binder .. (Code BAnon z%binder e%E) .. ))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'λ:' x y .. z , '/ ' e ']'") : val_scope.

(* This allows using tuple notation to construct a list of the formal
   parameters. *)

Notation "[[]]" :=
  (nil)
: binder_scope.

Notation "[[ x1 , .. , xn ]]" :=
  (cons (BNamed x1) (.. (cons (BNamed xn) nil) .. ))
: binder_scope.


(* ------------------------------------------------------------------------ *)

(* Sequencing. *)

Notation "'let:' x := e1 'in' e2" := (Let x%binder e1%E e2%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Notation "e1 ;; e2" :=
  (Let BAnon e1%E e2%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '['  e1  ']' ;; ']'  '/' e2 ']'")
: expr_scope.

(* ------------------------------------------------------------------------ *)

(* If. *)

Notation "'if:'  e1  'then'  e2  'else'  e3" :=  (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.

(* ------------------------------------------------------------------------ *)

(* Function calls. *)

Coercion Call : expr >-> Funclass.

(* This allows using tuple notation to construct a list of the actual
   parameters. *)

Notation "[[]]" :=
  (nil)
    : expr_scope.

Notation "[[ t1 , .. , tn ]]" :=
  (cons (t1 : expr)%V (.. (cons (tn : expr)%V nil) .. ))
    : expr_scope.


(* ------------------------------------------------------------------------ *)

Notation "'alloc' n" :=
  (Alloc (n%Z%V))
    (at level 10) : expr_scope.

Notation "src .[ ofs ]" :=
  (Load src%V ofs%Z%V)
    (at level 10, format "src .[ ofs ]") : expr_scope.

Notation "dst .[ ofs ] <- src" :=
  (Store dst%V ofs%Z%V src)
    (at level 10, format "dst .[ ofs ]  <-  src") : expr_scope.

(* ------------------------------------------------------------------------ *)
(* Op *)

Notation "x '+ y" :=
  (CallPrim (PrimIntOp IntAdd) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x '- y" :=
  (CallPrim (PrimIntOp IntSub) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x '* y" :=
  (CallPrim (PrimIntOp IntMul) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x '/ y" :=
  (CallPrim (PrimIntOp IntDiv) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x 'mod y" :=
  (CallPrim (PrimIntOp IntMod) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x 'min y" :=
  (CallPrim (PrimIntOp IntMin) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x 'max y" :=
  (CallPrim (PrimIntOp IntMax) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x '< y" :=
  (CallPrim (PrimIntCmp IntLt) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x '≤ y" :=
  (CallPrim (PrimIntCmp IntLe) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x '> y" :=
  (CallPrim (PrimIntCmp IntGt) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x '≥ y" :=
  (CallPrim (PrimIntCmp IntGe) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x '== y" :=
  (CallPrim (PrimEq) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x '&& y" :=
  (CallPrim (PrimBoolOp BoolAnd) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.

Notation "x '|| y" :=
  (CallPrim (PrimBoolOp BoolOr) (x:expr)%E (y:expr)%E)
    (at level 10 ) : expr_scope.
