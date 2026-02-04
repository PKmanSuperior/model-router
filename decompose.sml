signature DECOMP =
sig
    val split: Trs.reach list -> Trs.reach list list
    val delete: (Trs.ctrs * Trs.reach list) -> Trs.ctrs
    val decompose: Trs.ctrs * Trs.reach list -> (Trs.ctrs * Trs.reach list) list
end

structure Decomp : DECOMP =
struct
local
    structure T = Term
    structure LU = ListUtil
in

fun vars reachs = List.map (fn reach => (reach, Trs.vars reach)) reachs

fun intersects (xs, ys) = List.exists (fn x => LU.member x ys) xs
				      
fun groupIntersects (g1, g2) = List.exists (fn (_,bs1) => List.exists (fn (_,bs2) => intersects (bs1, bs2)) g2) g1
					   
fun insertGroup (g, []) = [g]
  | insertGroup (g, g'::gs) = if groupIntersects (g, g')
			      then insertGroup (g @ g', gs)
			      else g'::insertGroup (g, gs)
						   
fun normalize groups =
    let val groups' = foldl insertGroup [] groups
    in if length groups' = length groups
       then List.map (fn group => List.map (fn (a,_) => a) group) groups
       else normalize groups'
    end
	
fun split reachs =
    let val _ = print ("    " ^ Trs.prReachs reachs ^ "\n==> ")
	val reachsList = normalize (List.map (fn x => [x]) (vars reachs))
	val _ = print (String.concatWith ",\n    " (List.map Trs.prReachs reachsList) ^ "\n--------------------\n")
    in reachsList
    end 

fun partitionRules (ctrs, t) = 
    let val ps = T.pos t
	fun isMatch (l, r) t ps = List.exists (fn p => T.root l = T.root (T.subterm t p)) ps
    in List.partition (fn (rule, conds) => isMatch rule t ps) ctrs
    end

fun getUsableRules ([], t) = []
  | getUsableRules (ctrs, t) =
    let fun main ((rule, conds), rest) =
	    let val rh = (fn (l, r) => r) rule
	    in getUsableRules (rest, rh)
	    end
	val (ur, rest) = partitionRules (ctrs, t)
    in LU.union (ur, LU.unionMap (fn rule => main (rule, rest)) ur)
    end

fun isGround reachs = List.all (fn (s, t) => T.isGround s) reachs

fun delete (ctrs, reachs) =
    let val _ = print (Trs.prStatus (ctrs, reachs))
	val usableRules = List.map (fn (s, t) => getUsableRules (ctrs, s)) reachs
	val usableRulesSet = if isGround reachs then LU.unions usableRules else ctrs
	val _ = print (Trs.prCRulesDef "==> " usableRulesSet)
    in usableRulesSet
    end

fun decompose (ctrs, reachs) =
    let val _ = print "split:\n"
	val reachsList = split reachs
	val _ = print "delete:\n"
    in List.map (fn rc => (delete (ctrs,rc), rc)) reachsList
    end

end
end 
