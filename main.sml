signature MAIN =
sig
    val main: (Trs.ctrs * Trs.reach list) -> int -> bool
    val sub: (Trs.ctrs * Trs.reach list) -> bool
    val all: (string -> bool) -> string -> unit
end

    
fun bench label (f : 'a -> 'b) (x: 'a) : 'b =
  let
    val t = Timer.startCPUTimer ()
    val y = f x
    val {usr, ...} = Timer.checkCPUTimer t
  in
    print (label ^ " " ^ Time.toString usr ^ "\n");
    y
  end


structure Main : MAIN =
struct
local
    structure LU = ListUtil
    structure F = Form
in

fun select (ctrs, reachs) timeout =
    let val _ = print "FOL eocoding(replace '->' => 'P', '->*' => 'Q'):\n"
	val forms = Trans.getTheory ctrs @ [Trans.getInfeasibility reachs]
	val formsStr = Form.prForms forms
	val _ = print (Trs.prStatus (ctrs, reachs) ^ "==>" ^ String.substring (formsStr, 3, size formsStr - 3) ^ "--------------------\n")
    in if Criterion.proc ctrs reachs then Ages.ages forms timeout else Mace.mace forms (timeout div 2) orelse Ages.ages forms (timeout div 2)
    end

fun sub (ctrs, reachs) =
    let val problems = Decomp.decompose (ctrs,reachs)
    in List.exists (fn (R, p) => Criterion.proc R p) problems
    end 
																	     
fun main (ctrs, reachs) timeout =
    let val _ = print (Trs.prCRulesDef "R = " ctrs ^ "\nStart verifying whether " ^ Trs.prReachs reachs ^ " is R-infeasible.\n--------------------\n")
	val problems = Decomp.decompose (ctrs,reachs)
	val _ = print ("\n" ^ "ordering check:\n")
    in if List.exists Order.ordInf problems
       then
	   let val _ = print ("--------------------\n" ^ Trs.prReachs reachs ^ " is R-infeasible\n")
	   in true
	   end
       else
	   let val _ = print "--------------------\n"
	   in if List.exists (fn problem => select problem (timeout div (length problems))) problems
	      then
		  let val _ = print ("--------------------\n" ^ Trs.prReachs reachs ^ " is R-infeasible.\n")
		  in true
		  end
	      else
		  let val _ = print ("--------------------\n" ^ "R-infeasibility of " ^ Trs.prReachs reachs ^ " is unknown.\n")
		  in false
		  end
	   end 
    end 

fun all f directry =
    let val dir = OS.FileSys.openDir directry
	val outStream = TextIO.openOut "result.txt"
	fun read () = case OS.FileSys.readDir dir of
			  NONE => []
			| SOME file => file :: (read ())
	fun sort [] = []
	  | sort ss =
	    let val pivot = hd ss
		val rest = tl ss
		val (left, right) = List.partition (fn s => valOf (Int.fromString (String.substring (s, 0, size s - 4))) < valOf (Int.fromString (String.substring (pivot, 0, size pivot - 4)))) rest
	    in sort left @ (pivot :: sort right)
	    end
	fun loop [] = ()
	  | loop (file::rest) =
	    let val path = directry ^ "/" ^ file
		val _ = print (file ^ "\n")
		val result = f path
		val status = if result then TextIO.output (outStream, file ^ ": true\n") else TextIO.output (outStream, file ^ ": false\n")
	    in loop rest
	    end
	val files = sort (read ())
	val _ = loop files
	val _ = OS.FileSys.closeDir dir
	val _ = TextIO.closeOut outStream
    in ()
    end
	
end
end 
