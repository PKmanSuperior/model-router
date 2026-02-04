signature ORDER =
sig
    val isDecCtrs: Trs.ctrs -> bool
    val leReachs: Trs.reach list -> bool
    val ordInf: (Trs.ctrs * Trs.reach list) -> bool 
end

structure Order : ORDER =
struct
local
    structure T = Term
    structure LU = ListUtil
    structure AL = AssocList
in

fun varsSub [] ys = []
  | varsSub ((x, n)::xs) ys = case AL.find x ys of
				  SOME m => (n - m)::varsSub xs ys
				| NONE => n::varsSub xs ys
						     
fun sum [] = 0
  | sum (x::xs) = x + sum xs
			  
fun sizegt (s,t) =
    let val varsSubList = varsSub (T.varsNum s) (T.varsNum t)
	val funsSub = T.funsNum t - T.funsNum s 
	val cond1 = LU.isSubset (T.vars t, T.vars s)
	val cond2 = List.all (fn n => n >= 0) varsSubList 
	val cond3 = funsSub < sum varsSubList
    in cond1 andalso cond2 andalso cond3
    end

fun sizele (s,t) =
    let val varsSubList = varsSub (T.varsNum t) (T.varsNum s)
	val funsSub = T.funsNum s - T.funsNum t 
	val cond1 = LU.isSubset (T.vars s, T.vars t)
	val cond2 = List.all (fn n => n >= 0) varsSubList 
	val cond3 = funsSub <= sum varsSubList
    in cond1 andalso cond2 andalso cond3
    end

fun isDecCtrs [] = true
  | isDecCtrs ((rule, conds)::rest) = if sizegt rule orelse List.exists (fn cond => not (Subst.isUnif cond) andalso sizele cond) conds
				      then isDecCtrs rest
				      else false

fun leReachs reachs = List.exists (fn reach => not (Subst.isUnif reach) andalso sizele reach) reachs
					       
fun ordInf (ctrs, reachs) =
    let val _ = print (Trs.prStatus (ctrs, reachs))
    in if isDecCtrs ctrs andalso leReachs reachs
       then
	   let fun prSize t = "|[" ^ Term.toString t ^ "]|"
	       fun prGt (s,t) = prSize s ^ " > " ^ prSize t
	       fun prLe (s,t) = prSize s ^ " <= " ^ prSize t
	       fun prDec [] = []
		 | prDec ((rule,conds)::rest) =
		   let val le = List.filter (fn cond => not (Subst.isUnif cond) andalso sizele cond) conds
		   in if sizegt rule then (prGt rule ^ "\n")::prDec rest else (Trs.prCRule (rule, conds) ^ ": " ^ prLe (hd le) ^ "\n")::prDec rest
		   end 
	       val le = List.filter (fn reach => not (Subst.isUnif reach) andalso sizele reach) reachs
	       val _ = print "==> SUCCESS\n"
	       val _ = if null ctrs then print ("    " ^ prLe (hd le)) else print ("    " ^ String.concatWith "    " (prDec ctrs) ^ "    " ^ prLe (hd le))
	       val _ = print ("\n    " ^ Trs.prReachs reachs ^ " is infeasible.\n")
	   in true
	   end 
       else
	   let val _ = print "==> FAILURE\n"
	   in false
	   end 
    end 
					       
end
end 
