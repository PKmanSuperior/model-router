signature TRANS =
sig
    val getTheory: Trs.ctrs -> Form.form list
    val getInfeasibility: Trs.reach list -> Form.form
end

structure Trans : TRANS =
struct
local
    structure LU = ListUtil
    structure T = Term
    structure F = Form
in

fun getFuns [] = []
  | getFuns (((l,r),conds)::rest) =
    let val funsRule = LU.union (T.getAr l, T.getAr r)
	val funsConds = LU.unionMap (fn (s,t) => LU.union (T.getAr s, T.getAr t)) conds
    in LU.union (LU.union (funsRule, funsConds), getFuns rest)
    end 

fun getCongs ctrs =
    let fun getCong (f, k) =
	    let fun getArgs k var n i = if i <= k
					then if n = i
					     then T.Var var::(getArgs k var n (i + 1))
					     else T.Var ("x", i)::(getArgs k var n (i + 1))
					else []
		val fxs = List.tabulate (k, fn x => T.Fun (f, getArgs k ("x", 0) (x + 1) 1))
		val fys = List.tabulate (k, fn x => T.Fun (f, getArgs k ("y", 0) (x + 1) 1))
	    in List.map (fn (fx,fy) => F.Imp (F.Atom (F.Pred ("P", [T.Var ("x", 0), T.Var ("y", 0)])), F.Atom (F.Pred ("P", [fx,fy])))) (ListPair.zip (fxs, fys))
	    end 
	val funs = getFuns ctrs
    in List.concatMap getCong (List.filter (fn (f,k) => k > 0) funs)
    end

fun rename form =
    let val vars = F.vars form
	val dict = ListPair.zip (vars,List.tabulate (length vars, fn x => ("x", x + 1)))
	fun replaceVars [] form = form
	      | replaceVars ((var, xi)::rest) form =
		let fun replaceVarTerm (var, xi) (T.Var x) = if x = var then T.Var xi else T.Var x
		      | replaceVarTerm (var, xi) (T.Fun (f, ts)) = T.Fun (f, List.map (fn t => replaceVarTerm (var,  xi) t) ts)
		    fun replaceVar (F.Atom (F.Pred (p, ts))) = F.Atom (F.Pred (p, List.map (fn t => replaceVarTerm (var, xi) t) ts))
		      | replaceVar (F.Atom (F.Eq (l, r))) = F.Atom (F.Eq (replaceVarTerm (var, xi) l, replaceVarTerm (var, xi) r))
		      | replaceVar (F.Atom (F.Neq (l, r))) = F.Atom (F.Neq (replaceVarTerm (var, xi) l, replaceVarTerm (var, xi) r))
		      | replaceVar (F.Not p) = F.Not (replaceVar p)
		      | replaceVar (F.And (p, q)) = F.And (replaceVar p, replaceVar q)
		      | replaceVar (F.Or (p, q)) = F.Or (replaceVar p, replaceVar q)
		      | replaceVar (F.Imp (p, q)) = F.Imp (replaceVar p, replaceVar q)
		      | replaceVar (F.Iff (p, q))= F.Iff (replaceVar p, replaceVar q)
		      | replaceVar (F.All (x, p)) = F.All (x, replaceVar p)
		      | replaceVar (F.Exists (x, p)) = F.Exists (x, replaceVar p)
		in replaceVars rest (replaceVar form)
		end 
    in replaceVars dict form
    end

fun getRepls [] = []
  | getRepls (((l,r),conds)::rest) =
    let fun getConds [] = raise Fail "Error: condtion parts is empty"
	  | getConds [(s,t)] = F.Atom (F.Pred ("Q", [s,t]))
	  | getConds ((s,t)::rest) = F.And (F.Atom (F.Pred ("Q", [s,t])), getConds rest)
    in if null conds
       then rename (F.Atom (F.Pred ("P", [l,r]))) ::getRepls rest
       else rename (F.Imp (getConds conds, F.Atom (F.Pred ("P", [l,r])))) :: getRepls rest
    end 

fun getTheory ctrs =
    let val refl = F.Atom (F.Pred ("Q", [T.Var ("x", 0), T.Var ("x", 0)]))
	val trans = F.Imp (F.And (F.Atom (F.Pred ("P", [T.Var ("x", 0), T.Var ("y", 0)])), F.Atom (F.Pred ("Q", [T.Var ("y", 0), T.Var ("z", 0)]))), F.Atom (F.Pred ("Q", [T.Var ("x", 0), T.Var ("z", 0)])))
	val congs = getCongs ctrs
	val repls = getRepls ctrs
    in List.map F.addQuantsAll (refl::trans::congs @ repls)
    end 

fun getInfeasibility reachs =
    let fun main [] = raise Fail "Error: problem is empty"
	  | main [(s,t)] = F.Not (F.Atom (F.Pred ("Q", [s,t])))
	  | main ((s,t)::rest) = F.Or (F.Not (F.Atom (F.Pred ("Q", [s,t]))), main rest)
    in (F.addQuantsAll o rename o main) reachs
    end 

end
end
